-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_8_17
-- name    : MatMulDS.Supplement.theorem_8_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:22:25.724208+00:00
-- url     : https://prove2.me/theorems/4449db32-14a3-492d-ac66-f3d4f1422112
-- title:
--   Theorem 8.17 — fully dynamic $(1+\varepsilon)$-approximate distances on $S\times V$ with $(n^{3/2-\xi}+|S|n)n^{o(1)}$ updates
-- statement:
--   Let $\beta$ be an admissible saving, set $\xi=\beta(1-2\beta)/2$, and fix $\varepsilon\in(0,1)$. Using the bounds (3.3) of [Uzn26], for an undirected unweighted graph $G=(V,E)$ with $n$ vertices and a fixed set $S\subseteq V$, there is a deterministic data structure that maintains explicitly $(1+\varepsilon)$-approximations to all distances on $S\times V$ under edge insertions and deletions, with $n^{\omega+o(1)}$ initialization time and worst-case update time
--   $$(n^{3/2-\xi}+|S|n)\,n^{o(1)}=(n^{1.4998668}+|S|n)\,n^{o(1)}.$$
--   A stored distance is returned in constant time on the word RAM.
--
--   With the previous algebraic tools the same algorithm needed $(n^{3/2}+|S|n)n^{o(1)}$ per update.
--
--   Differences from the source:
--   - generalization: an algorithm on the word RAM with $\Theta(\log n)$-bit words → one word program of the mission's machine for every word size $w\ge K\lceil\log_2(n+1)\rceil+K$, all steps counted; reason: it specializes to each word size above the threshold and cannot exploit a huge word
--   - reading: "Using the bounds (3.3) of [Uzn26]" → no hypothesis; reason: it names a cited theorem the proof uses; assuming it would weaken the statement (SUPPLEMENT decision 2)
--   - encoding: operations, "maintains explicitly", "returned in constant time" → insert or delete $uv$ with $u\ne v$ (words $0$ or $1$, then $u,v$), or return the stored estimate for $(S_k,v)$ (words $2,k,v$, answer in word cell $-1$, $-1$ for $\infty$) within $K_q$ steps, a constant fixed before $n$; persistent memories (`DynOK`); reason: a constant-time return can only read a stored value; a layout
--   - generalization: edge insertions and deletions → insertion of an existing edge and deletion of an absent one are also allowed; reason: no-op updates; the source's sequences are a special case
--   - reading: $n^{\omega+o(1)}$ initialization and $n^{o(1)}$ update factor → one program, and for every $\eta>0$ a $C$ with $Cn^{\omega+\eta}$ and $C(n^{3/2-\xi}+|S|n)n^\eta$, $\omega=$ `omegaExp ℚ 1 1 1`; reason: the stronger reading: one data structure
--   - encoding: $(1+\varepsilon)$-approximation of a distance → `ApproxCode` $(1+\varepsilon)$ $0$: $d\le\tilde d\le(1+\varepsilon)d$, and $\infty$ for $\infty$; the initial graph arbitrary, by adjacency lists; reason: footnote 16
--   - encoding: the numerical form $n^{1.4998668}$ → a separate conjunct, the inequality at $\beta=0.0002666$; reason: the source evaluates its bound at the admissible saving of Theorem 7.4
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 8.17, p.60 (PDF p.62)

import Mathlib
import Definitions.Def_MatMulDS_omegaExp
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
import Definitions.Def_MatMulDS_Supplement_DynOK
import Definitions.Def_MatMulDS_Supplement_adjWords

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 8.17, p.60** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `β` be an
admissible saving, set `ξ = β(1 − 2β)/2`, and fix `ε ∈ (0, 1)`. Using the bounds (3.3) of [Uzn26], for an undirected unweighted
graph `G = (V, E)` with `n` vertices and a fixed set `S ⊆ V`, there is a deterministic data structure that maintains explicitly
`(1 + ε)`-approximations to all distances on `S × V` under edge insertions and deletions, with `n^{ω+o(1)}` initialization time and
worst-case update time `(n^{3/2−ξ} + |S|n) n^{o(1)} = (n^{1.4998668} + |S|n) n^{o(1)}`. A stored distance is returned in constant
time on the word RAM.

**Formalization Note.**
* Word programs of the published machine (deterministic word RAM), all steps counted, every word size `w ≥ K⌈log₂(n+1)⌉ + K`.
  The initialization reads the initial graph (adjacency lists `L` of `G₀`) and the list `S` without repetitions. The graph is the
  abstract state.
* An operation is `inl (true, u, v)`, insert `uv`, `inl (false, u, v)`, delete `uv` (words `0` or `1`, then `u, v`; valid when
  `u ≠ v`), or `inr (k, v)`, return the stored estimate for `(S_k, v)` (words `2, k, v`; the answer in word cell `−1`, `−1` for `∞`).
  A query takes at most `K_q` steps, a constant fixed before `n`: "returned in constant time"; the estimate is a
  `(1 + ε)`-approximation of `d_G(S_k, v)` in the current graph (`ApproxCode`, `∞` for `∞`).
* `n^{o(1)}`: one program, and for every `η > 0` a constant `C` with initialization within `C n^{ω+η}` (`ω = omegaExp ℚ 1 1 1`) and
  updates within `C (n^{3/2−ξ} + |S| n) n^η`. The numerical form (`β = 0.0002666`) is the last conjunct. -/
theorem theorem_8_17 (β : ℝ) (hβ : AdmissibleSaving β) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∃ (Pinit Pop : List AInstr) (K Kq : ℕ), IsWordProgram Pinit ∧ IsWordProgram Pop ∧
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ (G₀ : SimpleGraph (Fin n)) (L : Fin n → List (Fin n)), IsAdjRep G₀ L →
        ∀ S : List (Fin n), S.Nodup → ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
        ∃ m₀ : ℤ → BitVec w,
          wordRun Pinit w (adjWords L ++ vtxWords S) ⌈C * (n : ℝ) ^ (omegaExp ℚ 1 1 1 + η)⌉₊ = some m₀ ∧
          ∀ ops : List ((Bool × Fin n × Fin n) ⊕ (Fin S.length × Fin n)),
            DynOK (S := SimpleGraph (Fin n)) (M := (ℤ → BitVec w) × (ℤ → ℚ))
              (fun m op t m' =>
                let m₁ := withOp m (Sum.elim
                  (fun e => [if e.1 then 0 else 1, ((e.2.1 : ℕ) : ℤ), ((e.2.2 : ℕ) : ℤ)])
                  (fun q => [2, ((q.1 : ℕ) : ℤ), ((q.2 : ℕ) : ℤ)]) op) []
                aexec Pop (fun _ => 0) t 0 0 m₁.1 m₁.2 = some m')
              (fun _ op => Sum.elim (fun e => e.2.1 ≠ e.2.2) (fun _ => True) op)
              (fun G op => Sum.elim
                (fun e => if e.1 then G ⊔ SimpleGraph.edge e.2.1 e.2.2 else G.deleteEdges {s(e.2.1, e.2.2)})
                (fun _ => G) op)
              (fun G op m' => Sum.elim (fun _ => True)
                (fun q => ApproxCode (1 + ε) 0 (distCode G S[q.1] q.2) (m'.1 (-1)).toInt) op)
              (fun _ op _ => Sum.elim
                (fun _ => C * ((n : ℝ) ^ ((3 : ℝ) / 2 - β * (1 - 2 * β) / 2) + S.length * n) * (n : ℝ) ^ η)
                (fun _ => (Kq : ℝ)) op)
              G₀ (m₀, aloadFields []) ops) ∧
    (3 : ℝ) / 2 - 0.0002666 * (1 - 2 * 0.0002666) / 2 ≤ 1.4998668 := by sorry

end MatMulDS.Supplement
