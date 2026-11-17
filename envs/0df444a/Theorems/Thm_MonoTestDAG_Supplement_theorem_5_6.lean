-- Prove2me | Theorems.Thm_MonoTestDAG_Supplement_theorem_5_6
-- name    : MonoTestDAG.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:50:40.775045+00:00
-- url     : https://prove2.me/theorems/daeccf57-90ef-47a7-b50d-b8465b21a1c3
-- title:
--   Theorem 5.6 — $m^{1/3-\delta}/\varepsilon^{2/3}$ lower bound with two-sided error
-- statement:
--   For every constant $\delta>0$, there are constants $c_\delta,\varepsilon_\delta>0$ such that, for every $\varepsilon\in(0,\varepsilon_\delta)$ and infinitely many values of $m$, there is a transitively reduced DAG $G$ with exactly $m$ edges for which every randomized non-adaptive $\varepsilon$-tester for monotonicity, even with two-sided error, makes at least
--
--   $$
--   c_\delta\frac{m^{1/3-\delta}}{\varepsilon^{2/3}}
--   $$
--
--   queries in the worst case.
--
--   This matches the $m^{1/3}/\varepsilon^{2/3}$ dependence of the paper’s first upper bound up to the arbitrarily small exponent loss $\delta$.
--
--   **Formalization Note.** The edge parameter is the published `numTR`; the separate `IsTransReduced` clause says these cover pairs are exactly the graph’s supplied edges.
--
--   Differences from the source:
--   - encoding: “infinitely many values of $m$” → for every threshold $M_0$ there is an integer $m\ge\max\{M_0,1\}$; reason: this is the quantified meaning of infinitude and excludes the real-power boundary at $m=0$
--   - encoding: a transitively reduced DAG with $m$ edges → `IsDAG E`, `IsTransReduced E`, and `numTR E = m`; reason: in a transitively reduced DAG the paper’s parameter $m$ is exactly its edge count
--   - encoding: a lower bound on the number of queries → the inequality is required for every real worst-case query budget $q$; reason: finite query counts are integers, so real upper bounds encode the same worst-case complexity without changing any tester instance
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Theorem 5.6, p.30 (PDF 32), proof p.31 (PDF 33)

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_numTR

namespace MonoTestDAG.Supplement

/-- **Theorem 5.6 (lower bound matching the m^(1/3) tester, even with two-sided error).**
For every constant `δ>0` there are constants `c_δ,ε_δ>0` such that, for every
`ε∈(0,ε_δ)` and infinitely many exact values of `m`, there is a transitively reduced DAG
with `m` edges on which every randomized non-adaptive two-sided `ε`-tester makes at least
`c_δ m^(1/3-δ)/ε^(2/3)` queries.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Theorem 5.6, pp.30–31.

**Formalization Note.** The constants precede `ε`, and "infinitely many values of `m`" is
`∀ M₀, ∃ m≥M₀`; `m≥1` excludes the real-power boundary at zero. The paper's edge count
is `numTR E`; `IsTransReduced E` says these cover pairs are exactly the supplied edges. -/
theorem theorem_5_6 :
    ∀ δ : ℝ, 0 < δ → ∃ cδ εδ : ℝ, 0 < cδ ∧ 0 < εδ ∧
      ∀ ε : ℝ, 0 < ε → ε < εδ → ∀ M₀ : ℕ,
        ∃ (m : ℕ) (V : Type) (_ : Fintype V) (_ : DecidableEq V)
          (E : V → V → Prop),
          M₀ ≤ m ∧ 1 ≤ m ∧ IsDAG E ∧ IsTransReduced E ∧ numTR E = m ∧
          ∀ (T : Tester V) (q : ℝ), IsTwoSidedTester E ε T → T.QueriesAtMost q →
            cδ * (m : ℝ) ^ (1 / 3 - δ) / ε ^ (2 / 3 : ℝ) ≤ q := by sorry

end MonoTestDAG.Supplement
