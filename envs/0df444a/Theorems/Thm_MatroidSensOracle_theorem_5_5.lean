-- Prove2me | Theorems.Thm_MatroidSensOracle_theorem_5_5
-- name    : MatroidSensOracle.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:31.530471+00:00
-- url     : https://prove2.me/theorems/9a0295b7-7b0c-4518-bf27-92250ac1d59b
-- title:
--   Theorem 5.5: exact $(s,t)$-max-flow, nearest min-cut and min-cost max-flow sensitivity oracles for $f$ edge updates
-- statement:
--   Let $\omega$ be the exponent of matrix multiplication. For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and three oracles $(P_i,Q_i)$ on the randomized word RAM such that the following holds for every $n\ge2$, $f\ge1$, $W\ge1$, every simple directed graph $G$ on $n$ vertices with integer edge costs in $[-W,W]$, every source $s$ and sink $t\ne s$, and every word width $w\ge b(\lfloor\log_2(n+f+W+2)\rfloor+1)$. Write $\ell_f=\log_2(f+1)+1$ and $\ell=\log_2(n+f+W+2)$.
--
--   1. **Max-Flow.** $P_1$ halts within $C(fn)^{\omega+\tau}$ steps and stores at most $C(fn)^2\log_2n$ bits; for every update set $U$ of at most $f$ insertions and deletions (inserted costs in $[-W,W]$), $Q_1$ halts within $Cf^4\ell_f^K$ steps and outputs $\lambda_{G+U}(s,t)$.
--   2. **Nearest Min-Cut.** The same preprocessing and space bounds; $Q_2$ halts within $Cf^4n\,\ell_f^K$ steps and outputs the source side of $\mathrm{NMC}_{G+U}(s,t)$.
--   3. **Min-Cost Flow.** $P_3$ halts within $CW(fn)^3\ell^K$ steps and stores at most $CW(fn)^3\log_2n$ bits; $Q_3$ halts within $Cf^5Wn\,\ell^K$ steps and outputs the minimum cost of an $(s,t)$-flow of value $\lambda_{G+U}(s,t)$ in $G+U$.
--
--   All times are worst case over the coins; each fixed query is answered wrongly with probability at most $n^{-c}$; $Q_i$ sees only the stored bits and $U$. The query times of the first two oracles depend on $f$ alone; this resolves for every $f$ the exact $(s,t)$-max-flow sensitivity problem of Baswana, Bhanja and Pandey.
--
--   Differences from the source:
--   - reading: sensitivity oracles in the Word-RAM model, randomized (machine details unstated) → the randomized word RAM: the published APSP instruction set plus unsigned div and mod and a uniform-below coin; programs correct for every word width w ≥ b(⌊log₂(n+f+W+2)⌋+1); reason: §2, p.13 (constant-time field arithmetic in the word RAM); the uniform coin makes worst-case time meaningful
--   - reading: Space O((fn)² log n); a query answered from the structure → space = bits of the string S stored by P; Q reads only S and the encoding of U and draws fresh coins; reason: O((fn)²) field elements of O(log n) bits; counting cells with free word width would trivialize space
--   - encoding: O((fn)^ω), ω the matrix multiplication exponent → C (fn)^{ω+τ} for every τ > 0, ω = omega ℂ; reason: ω is an infimum
--   - reading: Õ(f⁴), Õ(f⁴n); Õ(W(fn)³), Õ(f⁵Wn) → factors (log₂(f+1)+1)^K in rows 1–2 and (log₂(n+f+W+2))^K in row 3; reason: the query times of rows 1–2 depend on f only (abstract); the min-cost row inherits polylog(fnW) from Lemma 2.2
--   - reading: with high probability → for every c > 0, each fixed query is wrong with probability at most n^{−c} over the coins of P and Q; times worst case on every coin sequence; reason: the standard strong reading; constants and programs may depend on c
--   - reading: for any set U ∈ E^f; G + U := (V, (E \ F) ∪ I) → any update set U = (I, F) with F ⊆ E, |I| + |F| ≤ f and inserted costs in [−W, W]; G + U a multigraph (an inserted edge is a new edge); reason: §2 and Table 3 define mixed updates; the paper's constructions need parallel edges
--   - encoding: n-vertex graph, source s, sink t, costs in [−W, W]; log n → n ≥ 2, f ≥ 1, W ≥ 1, s ≠ t; log₂ n; reason: excludes only degenerate cases where the bounds vanish
--   - reading: G = (V, E, c) a directed graph → E ⊆ V × V: no parallel edges in the input; reason: the preprocessing bound O((fn)^ω) cannot read a multigraph with m ≫ n² edges; only G + U has parallel edges
--   - generalization: directed graph (self-loops not discussed) → self-loops (v, v) allowed in E; reason: loopless graphs are a special case; a loop changes no flow value or cut and adds its cost to the min-cost only when negative
--   - reading: outputs λ_{G+U}(s, t), NMC_{G+U}(s, t), min-cost max-flow → word 0 of Q's final memory (unsigned); the low bits of words 0, …, n − 1 as the source side; word 0 (signed) as the minimum cost of a flow of value λ_{G+U}(s, t), cycles allowed; reason: output layout; "min-cost max-flow" is reported as its cost, as the proof computes it (§5.2, p.30) and as the query time Õ(f⁵Wn), below the size of a flow on up to n² edges, requires
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 5.5, p.29 (PDF p.32); model §2, pp.12–13; with §5.2, pp.27–30

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_MatroidSensOracle_InputGraph
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle

/-- **Theorem 5.5.** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…),
p.29 (PDF p.32): "Let G = (V, E, c) be an n-vertex directed graph with integer edge costs in
[−W, W], and a designated source s and sink t. Then there exist the following sensitivity oracles
that, for any set U ∈ E^f, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Max-Flow | O((fn)^ω) | O((fn)² log n) | Õ(f⁴) | λ_{G+U}(s, t) |
| Nearest Min-Cut | O((fn)^ω) | O((fn)² log n) | Õ(f⁴n) | NMC_{G+U}(s, t) |
| Min-Cost Flow | Õ(W(fn)³) | O(W(fn)³ log n) | Õ(f⁵Wn) | Min-cost max-flow in G + U |

**Formalization Note.**
* **Machine:** the randomized word RAM `MatroidSensOracle.exec` (the published APSP word RAM's
  instructions plus `udiv`, `umod` and a uniform-below coin); every program works for every word width
  `w ≥ b(⌊log₂(n + f + W + 2)⌋ + 1)`.
* **Oracle:** `P` reads `encode G f W s t` (`n, f, W, s, t`, the edges with costs) and stores a bit
  string `S`; `Q` reads only `S` and `U.encode` and draws fresh coins (`Oracle.run`). Space is `|S|` in
  bits. Times are worst case over all coins.
* **ω** is `omega ℂ`, the exponent of matrix multiplication; `O(x^ω)` is `C x^{ω+τ}` for every `τ > 0`.
  `Õ` hides `(log₂(f + 1) + 1)^K` in the two first rows (their query times depend on `f` only) and
  `(log₂(n + f + W + 2))^K` in the third. `log n` is `log₂ n`.
* **With high probability:** for every `c > 0` (the constants and programs depend on `c` and `τ`), each
  fixed query is answered wrongly with probability at most `n^{−c}` over the coins of `P` and `Q`.
* **Instances:** `n ≥ 2`, `f ≥ 1`, `W ≥ 1`, `s ≠ t`; `G` simple (`E ⊆ V × V`) with costs in `[−W, W]`. A
  query is any update set `U = (I, F)`, `F ⊆ E`, `|I| + |F| ≤ f`, with inserted costs in `[−W, W]`
  ("U ∈ E^f": mixed insertions and deletions); `G + U` is a multigraph (an inserted edge is a new edge).
* **Outputs:** Max-Flow: word `0` of `Q`'s final memory (unsigned) is `λ_{G+U}(s, t)`. Nearest Min-Cut:
  the low bits of words `0, …, n − 1` are the indicator of the source side of `NMC_{G+U}(s, t)`.
  Min-Cost Flow: word `0` (signed) is the minimum cost of an `(s, t)`-flow of value `λ_{G+U}(s, t)` in
  `G + U` (cycles allowed). -/
theorem theorem_5_5 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ O₃ : Oracle),
      ∀ (n f W : ℕ) (G : InputGraph n) (s t : Fin n), 2 ≤ n → 1 ≤ f → 1 ≤ W → s ≠ t →
        G.CostsBounded W → ∀ w : ℕ, b * (Nat.log 2 (n + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := G.encode f W s t
          let err : ℝ := (n : ℝ) ^ (-c)
          let lgf : ℝ := Real.logb 2 ((f : ℝ) + 1) + 1
          let lgA : ℝ := Real.logb 2 ((n : ℝ) + f + W + 2)
          let fn : ℝ := (f : ℝ) * n
          let TP₁ : ℕ := ⌊C * fn ^ (ω + τ)⌋₊
          let TQ₁ : ℕ := ⌊C * (f : ℝ) ^ 4 * lgf ^ K⌋₊
          let TQ₂ : ℕ := ⌊C * (f : ℝ) ^ 4 * n * lgf ^ K⌋₊
          let TP₃ : ℕ := ⌊C * W * fn ^ 3 * lgA ^ K⌋₊
          let TQ₃ : ℕ := ⌊C * (f : ℝ) ^ 5 * W * n * lgA ^ K⌋₊
          -- Max-Flow
          (O₁.PrepWithin w inp TP₁ (C * fn ^ 2 * Real.logb 2 n) ∧
            ∀ U : Update n, G.ValidUpdate f W U →
              O₁.QueryWithin w inp U.encode TP₁ TQ₁ ∧
              O₁.ErrorAtMost w inp U.encode TP₁ TQ₁
                (fun mQ => (mQ 0).toNat = (G.plus U).maxFlow s t) err) ∧
          -- Nearest Min-Cut
          (O₂.PrepWithin w inp TP₁ (C * fn ^ 2 * Real.logb 2 n) ∧
            ∀ U : Update n, G.ValidUpdate f W U →
              O₂.QueryWithin w inp U.encode TP₁ TQ₂ ∧
              O₂.ErrorAtMost w inp U.encode TP₁ TQ₂
                (fun mQ => (G.plus U).IsNearestMinCut s t
                  (Finset.univ.filter fun v : Fin n => (mQ (v : ℕ)).getLsbD 0 = true)) err) ∧
          -- Min-Cost Flow
          (O₃.PrepWithin w inp TP₃ (C * W * fn ^ 3 * Real.logb 2 n) ∧
            ∀ U : Update n, G.ValidUpdate f W U →
              O₃.QueryWithin w inp U.encode TP₃ TQ₃ ∧
              O₃.ErrorAtMost w inp U.encode TP₃ TQ₃
                (fun mQ => ((mQ 0).toInt : WithTop ℤ) =
                  (G.plus U).minCostFlow s t ((G.plus U).maxFlow s t)) err) := by sorry

end MatroidSensOracle
