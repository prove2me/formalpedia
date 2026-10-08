-- Prove2me | Theorems.Thm_KingmanSubadditive_PositiveMatrices_S3_bound
-- name    : KingmanSubadditive.PositiveMatrices.S3_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:05.602396+00:00
-- url     : https://prove2.me/theorems/a3c6fa4c-b329-4a32-be00-43cd3b2a62ca
-- title:
--   Proof of Theorem 5, p. 892 — E log‖Y₁‖ is finite and g_n/n ≥ −E log‖Y₁‖, so S₃ holds
-- statement:
--   Assume the hypotheses of Theorem 5, and let $\|A\|=\max_i\sum_j|[A]_{ij}|$ be the $\ell_1$-norm (maximum absolute row sum). Then $\log\|Y_1\|$ has finite expectation and, with $g_n=E(x_{0n})=-E\{\log [Y_1\cdots Y_n]_{11}\}$,
--   $$\frac{g_n}{n}\ \ge\ -E\{\log\|Y_1\|\}\qquad\text{for every } n\ge1 .$$
--   Hence $\inf_n g_n/n>-\infty$ and the process $x_{st}=-\log [Y_{s+1}\cdots Y_t]_{11}$ satisfies condition S₃ of §1.1.
--
--   **Formalization Note.** The infimum is stated as the bound $g_n\ge -n\,E\{\log\|Y_1\|\}$ for every $n\ge1$.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 892, §2.2, proof of Theorem 5

import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology

namespace KingmanSubadditive.PositiveMatrices

/-- Proof of Theorem 5, p. 892 (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973)), unnumbered: with `‖A‖ = max_i Σ_j |[A]_ij|` the ℓ₁-norm,
`E{log ‖Y₁‖} < ∞` and `inf g_n/n ≥ −E{log ‖Y₁‖} > −∞`, so S₃ is satisfied by
`x_st = −log [Y_{s+1} ⋯ Y_t]₁₁`.

**Formalization Note.** "`E{log ‖Y₁‖}` is finite" is integrability of `log ‖Y₁‖`
(`‖Y₁‖ > 0` under positivity, so the logarithm is the genuine one). The infimum over `n ≥ 1` is
written as the bound `g_n ≥ −n·E{log ‖Y₁‖}` for every `n ≥ 1`, which is equivalent and avoids
Lean's junk value for an unbounded real infimum. -/
theorem S3_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    Integrable (fun ω => Real.log (rowSumNorm (Y 1 ω))) P ∧
    ∀ n : ℕ, 1 ≤ n →
      -((n : ℝ) * ∫ ω, Real.log (rowSumNorm (Y 1 ω)) ∂P) ≤ g P (x Y) n := by sorry

end KingmanSubadditive.PositiveMatrices
