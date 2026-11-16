-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_8_15
-- name    : MatMulDS.Supplement.theorem_8_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:21:44.192336+00:00
-- url     : https://prove2.me/theorems/cfe34b07-477c-4f68-9a66-273478eae4fa
-- title:
--   Theorem 8.15 — incremental path reporting: $\tilde O(n^{3/2-\xi})$ insertions, $\tilde O(n^{1/2-\xi'})+O(|P|)$ queries
-- statement:
--   Let $\beta$ be an admissible saving, and set $\xi=\beta(1-2\beta)/2$ and $\xi'=\beta(1-\beta)/2$. Using the bounds (3.3) of [Uzn26], there is a deterministic data structure for a directed graph with $n$ vertices that, after $n^{\omega+o(1)}$ initialization time, supports edge insertions in $\tilde O(n^{3/2-\xi})=\tilde O(n^{1.4998668})$ time and reports a simple path $P$ between any queried pair of vertices, or reports that none exists, in
--   $$\tilde O(n^{1/2-\xi'})+O(|P|)=\tilde O(n^{0.4998668})+O(|P|)$$
--   time. The bounds are worst-case on the word RAM.
--
--   The update and query bounds both beat the conditional lower bound under the Mv-hinted Mv conjecture, which Theorem 8.8 refutes.
--
--   Differences from the source:
--   - generalization: an algorithm on the word RAM with $\Theta(\log n)$-bit words → one word program of the mission's machine for every word size $w\ge K\lceil\log_2(n+1)\rceil+K$, all steps counted; reason: it specializes to each word size above the threshold and cannot exploit a huge word
--   - reading: "Using the bounds (3.3) of [Uzn26]" → no hypothesis; reason: it names a cited theorem the proof uses; assuming it would weaken the statement (SUPPLEMENT decision 2)
--   - reading: "a directed graph with $n$ vertices" at initialization → an arbitrary initial graph $G_0$, given by out-neighbour lists; reason: Lemma G.1 initializes from $G_0$ ("the trees $T_v$ of $G_0$")
--   - encoding: operations and answers → insert $uv$ (words $0,u,v$) or query $(u,v)$ (words $1,u,v$); the answer: in word cell $-1$ the number $k$ of vertices of the path ($0$ for none) and the distinct vertices $u=x_0,\dots,x_{k-1}=v$, joined by edges of the current graph, in cells $-2,-3,\dots$; persistent memories (`DynOK`); reason: a layout; a simple path is a list of distinct vertices
--   - encoding: $\tilde O(n^{1/2-\xi'})+O(|P|)$ → $C(\log n+1)^cn^{1/2-\xi'}+Ck$ with $k=|P|+1$; reason: the same bound, as the first term is at least $C$
--   - generalization: edge insertions → insertions of any pair, including an existing edge; reason: a no-op insertion is allowed; the source's sequences are a special case
--   - reading: $n^{\omega+o(1)}$ initialization → one program, for every $\varepsilon>0$ a $C_\varepsilon$ with $C_\varepsilon n^{\omega+\varepsilon}$, $\omega=$ `omegaExp ℚ 1 1 1`, other constants fixed before $\varepsilon$; reason: the stronger reading: one data structure
--   - encoding: the numerical form $\tilde O(n^{1.4998668})$, $\tilde O(n^{0.4998668})$ → a separate conjunct, the inequality at $\beta=0.0002666$; reason: the source evaluates its bound at the admissible saving of Theorem 7.4
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 8.15, p.59 (PDF p.61); Lemma G.1, p.109

import Mathlib
import Definitions.Def_MatMulDS_omegaExp
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
import Definitions.Def_MatMulDS_Supplement_DynOK
import Definitions.Def_MatMulDS_Supplement_adjWords

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 8.15, p.59** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `β` be an
admissible saving, and set `ξ = β(1 − 2β)/2` and `ξ′ = β(1 − β)/2`. Using the bounds (3.3) of [Uzn26], there is a deterministic
data structure for a directed graph with `n` vertices that, after `n^{ω+o(1)}` initialization time, supports edge insertions in
`Õ(n^{3/2−ξ}) = Õ(n^{1.4998668})` time and reports a simple path `P` between any queried pair of vertices, or reports that none
exists, in `Õ(n^{1/2−ξ′}) + O(|P|) = Õ(n^{0.4998668}) + O(|P|)` time. The bounds are worst-case on the word RAM.

**Formalization Note.**
* Word programs of the published machine (deterministic word RAM), all steps counted, every word size `w ≥ K⌈log₂(n+1)⌉ + K`.
  The initialization reads the initial graph `G₀` (arbitrary, as in Lemma G.1: "the trees `T_v` of `G₀`") as out-neighbour lists
  `adjWords L`. The edge set is the abstract state.
* An operation is `inl (u, v)`, insert the edge `uv` (words `0, u, v`), or `inr (u, v)`, query (words `1, u, v`), written to the
  negative word cells (`withOp`). A query answers in word cell `−1` the number `k` of vertices of the path, `0` for "none", and in
  the cells `−2, −3, …` its vertices `u = x₀, …, x_{k−1} = v`, which are distinct and joined by edges of the current graph.
* The query bound is `C (log n + 1)^c n^{1/2−ξ′} + C k`; `k = |P| + 1`, so this is `Õ(n^{1/2−ξ′}) + O(|P|)`. `n^{ω+o(1)}`: for every
  `ε > 0` some `C_ε` with `C_ε n^{ω+ε}`, `ω = omegaExp ℚ 1 1 1`, the other constants fixed before `ε`.
* "Using the bounds (3.3) of [Uzn26]" names a cited theorem; it is not a hypothesis. The numerical forms (`β = 0.0002666`) are the
  last conjunct. -/
theorem theorem_8_15 (β : ℝ) (hβ : AdmissibleSaving β) :
    (∃ (Pinit Pop : List AInstr) (K c : ℕ) (C : ℝ), 0 < C ∧ IsWordProgram Pinit ∧ IsWordProgram Pop ∧
      ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ L : Fin n → List (Fin n), (∀ v, (L v).Nodup) →
        ∀ w : ℕ, K * Nat.clog 2 (n + 1) + K ≤ w →
        ∃ m₀ : ℤ → BitVec w,
          wordRun Pinit w (adjWords L) ⌈Cε * (n : ℝ) ^ (omegaExp ℚ 1 1 1 + ε)⌉₊ = some m₀ ∧
          ∀ ops : List ((Fin n × Fin n) ⊕ (Fin n × Fin n)),
            DynOK (S := Finset (Fin n × Fin n)) (M := (ℤ → BitVec w) × (ℤ → ℚ))
              (fun m op t m' =>
                let m₁ := withOp m (Sum.elim (fun e => [0, ((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ)])
                  (fun e => [1, ((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ)]) op) []
                aexec Pop (fun _ => 0) t 0 0 m₁.1 m₁.2 = some m')
              (fun _ _ => True)
              (fun E op => Sum.elim (fun e => insert e E) (fun _ => E) op)
              (fun E op m' => Sum.elim (fun _ => True)
                (fun e =>
                  ((m'.1 (-1)).toInt = 0 ∧ ¬ Relation.ReflTransGen (fun a b => (a, b) ∈ E) e.1 e.2) ∨
                  ∃ path : List (Fin n), 1 ≤ path.length ∧ (m'.1 (-1)).toInt = path.length ∧ path.Nodup ∧
                    path.head? = some e.1 ∧ path.getLast? = some e.2 ∧
                    List.IsChain (fun a b => (a, b) ∈ E) path ∧
                    ∀ (t : ℕ) (ht : t < path.length), (m'.1 (-2 - t)).toInt = ((path[t] : ℕ) : ℤ)) op)
              (fun _ op m' => Sum.elim (fun _ => C * (Real.log n + 1) ^ c * (n : ℝ) ^ ((3 : ℝ) / 2 - β * (1 - 2 * β) / 2))
                (fun _ => C * (Real.log n + 1) ^ c * (n : ℝ) ^ ((1 : ℝ) / 2 - β * (1 - β) / 2) +
                  C * (max 0 (m'.1 (-1)).toInt : ℤ)) op)
              ((Finset.univ.filter fun e : Fin n × Fin n => e.2 ∈ L e.1)) (m₀, aloadFields []) ops) ∧
    (3 : ℝ) / 2 - 0.0002666 * (1 - 2 * 0.0002666) / 2 ≤ 1.4998668 ∧
    (1 : ℝ) / 2 - 0.0002666 * (1 - 0.0002666) / 2 ≤ 0.4998668 := by sorry

end MatMulDS.Supplement
