-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_smaller_side_transfer
-- name    : IndependentInfoPricing.Main.Supplement.smaller_side_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:56:14.587589+00:00
-- url     : https://prove2.me/theorems/911d6510-5ede-4201-86e3-b233e0f1390e
-- title:
--   Lemma 4.18 — Smaller-side transfer
-- statement:
--   In a fixed orthant (54) with $m,n\ge1$ whose magnitudes are independent and regular (scope of §4.4), with $\bar a=\sum_i\operatorname{Rev}(X_i)$ and $\bar b=\sum_j\operatorname{Rev}(Y_j)$,
--   $$\min\{\bar a,\bar b\}\le8\,\mathrm{SRev}_\pm,\tag{69}$$
--   where $\mathrm{SRev}_\pm=\max\{\mathrm{SRev}_+,\mathrm{SRev}_-\}$ is the two-sided separate-selling benchmark of the whole $Q$-coordinate instance.
--
--   Whichever block has the smaller classical separate revenue can be sold separately in the information problem, because the opposite aggregate shields the buyer from the free take-all option with probability at least $1/2$.
--
--   **Formalization Note** $\mathrm{SRev}_\pm$ is the base `sRevBoth` on the product law of the marginals.
--
--   Differences from the source:
--   - reading: a continuously differentiable density, positive throughout an interval support, with pointwise values at a finite left endpoint understood as right limits (possibly extended) → a density version f : ℝ → [0,∞] that is finite, positive and C¹ on the interior of the topological support, the support being an interval; the hazard η at the left endpoint is the liminf of t·f(t)/S(t) from the interior; reason: endpoint values are one-sided limits in the source, so positivity is imposed where the density is evaluated pointwise (the interior); the liminf equals the source's one-sided limit whenever that limit exists, which regularity guarantees
--   - encoding: regularity: ψ_D(t) = t − 1/h_D(t) nondecreasing on the support → ψ_D(t) = t − S_D(t)/f(t) monotone on the interior of the support; reason: the endpoint values of ψ_D are one-sided limits of interior values, so monotonicity on the interior is monotonicity on the support
--   - encoding: after re-indexing, v = (X_1,…,X_m,−Y_1,…,−Y_n) → a coordinate set S with v_i > 0 a.s. on S and v_j < 0 a.s. off S, both nonempty; reason: the same fixed orthant without re-indexing
--   - encoding: real expected revenues, suprema and probabilities → nonnegative extended reals (ℝ≥0∞): lintegrals, suprema and measures; reason: the base mission's convention; it represents every finite value unchanged and avoids default-zero integrals
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.18, printed p.42 (PDF p.44); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_Orthant

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Lemma 4.18, p.42 (PDF 44), (69): smaller-side transfer `min{ā, b̄} ≤ 8 SRev±`. -/
theorem smaller_side_transfer {Q : ℕ} (F : Marginals (Fin Q)) (S : Finset (Fin Q))
    (hF : RegularOrthant F S) :
    min (aBar F S) (bBar F S) ≤ 8 * sRevBoth (productLaw F) := by sorry


end IndependentInfoPricing.Main.Supplement
