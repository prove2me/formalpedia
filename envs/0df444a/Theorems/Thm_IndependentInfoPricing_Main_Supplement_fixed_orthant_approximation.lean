-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_fixed_orthant_approximation
-- name    : IndependentInfoPricing.Main.Supplement.fixed_orthant_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:56:51.112932+00:00
-- url     : https://prove2.me/theorems/8a398946-aeb6-44b5-acd3-6f87a6d14a23
-- title:
--   Theorem 4.11 — O(log Q) approximation in a fixed orthant
-- statement:
--   Consider the information-pricing problem in a fixed orthant (54): after re-indexing, $v=(X_1,\dots,X_m,-Y_1,\dots,-Y_n)$ with $m,n\ge1$, $m+n=Q$, and all magnitude variables $X_i,Y_j>0$ mutually independent and regular (positive continuously differentiable densities on interval supports, finite monopoly prices). Then
--   $$\mathrm{OPT}\le8\bigl(\ln(Q-1)+3\bigr)\,\mathrm{SRev}_\pm.\tag{55}$$
--
--   That is, two-sided separate selling is an $O(\log Q)$-approximation to the optimal fixed-orthant information-pricing mechanism. Since $m,n\ge1$, $Q\ge2$ and $\ln(Q-1)\ge0$.
--
--   **Formalization Note** $\mathrm{OPT}$ is the base `opt` (all response rules, both free outside options) and $\mathrm{SRev}_\pm$ the base `sRevBoth`, on the product law; the logarithm is natural.
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
--   - encoding: after re-indexing, v = (X_1,…,X_m,−Y_1,…,−Y_n) → a coordinate set S with v_i > 0 a.s. on S and v_j < 0 a.s. off S, both nonempty; reason: the same fixed orthant without re-indexing
--   - encoding: real expected revenues, suprema and probabilities → nonnegative extended reals (ℝ≥0∞): lintegrals, suprema and measures; reason: the base mission's convention; it represents every finite value unchanged and avoids default-zero integrals
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Theorem 4.11, printed p.36 (PDF p.38); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_Orthant

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Theorem 4.11, p.36 (PDF 38), (55): in a regular fixed orthant with `m, n ≥ 1`,
`OPT ≤ 8 (ln(Q − 1) + 3) SRev±`. -/
theorem fixed_orthant_approximation {Q : ℕ} (F : Marginals (Fin Q)) (S : Finset (Fin Q))
    (hF : RegularOrthant F S) :
    opt (productLaw F) ≤
      ENNReal.ofReal (8 * (Real.log ((Q : ℝ) - 1) + 3)) * sRevBoth (productLaw F) := by sorry


end IndependentInfoPricing.Main.Supplement
