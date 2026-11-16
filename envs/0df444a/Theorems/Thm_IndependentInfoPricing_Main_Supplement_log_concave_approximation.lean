-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_log_concave_approximation
-- name    : IndependentInfoPricing.Main.Supplement.log_concave_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:53:51.083765+00:00
-- url     : https://prove2.me/theorems/a2daf5bd-7b08-460e-bbae-81b38866440f
-- title:
--   Theorem 4.7 — Log-concave marginals: the constant 4e
-- statement:
--   Consider the information-pricing problem with $Q\ge1$ states and independent normalized payoff coordinates $v_1,\dots,v_Q$ of unrestricted signs. Assume that each $v_i$ has a continuously differentiable log-concave density, and that every magnitude branch occurring with positive probability ($\mathcal L(v_i\mid v_i>0)$ when $\Pr(v_i>0)>0$, $\mathcal L(-v_i\mid v_i<0)$ when $\Pr(v_i<0)>0$) has a finite monopoly price. Then
--   $$\mathrm{OPT}\le4e\,\widetilde{\mathrm{SRev}},$$
--   where $\widetilde{\mathrm{SRev}}$ is the symmetrized separate-selling benchmark (17): the best revenue of the reverse-closed symmetrization of an activation menu, which is implementable in the information problem.
--
--   No regularity, interval-support, half-tail or fixed-orthant assumption is made; this is the log-concave route to a constant-factor guarantee.
--
--   **Formalization Note** $\mathrm{OPT}$ is the base `opt` and $\widetilde{\mathrm{SRev}}$ the base `sRevSym`, on the product law of the marginals; $4e$ is `ENNReal.ofReal (4 * Real.exp 1)`. Continuous differentiability is required on the interior of the support of each marginal, as in the base `SmoothDensity`.
--
--   Differences from the source:
--   - encoding: real expected revenues, suprema and probabilities → nonnegative extended reals (ℝ≥0∞): lintegrals, suprema and measures; reason: the base mission's convention; it represents every finite value unchanged and avoids default-zero integrals
--   - encoding: Q states carrying a prior (Section 2) → explicit hypothesis 0 < Q; reason: a prior on Q states sums to 1, so the model has Q ≥ 1; Q = 0 is no instance of the source (and there OPT = 0), as in the base mission's half_tail_approximation and main_theorem
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Theorem 4.7, printed p.30 (PDF p.32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_LogConcave

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Theorem 4.7, p.30 (PDF 32): independent coordinates with continuously differentiable
log-concave densities, every occurring magnitude branch with a finite monopoly price, unrestricted
signs: `OPT ≤ 4e · SReṽ`. -/
theorem log_concave_approximation {Q : ℕ} (hQ : 0 < Q) (F : Marginals (Fin Q))
    (hF : ProbabilityMarginals F) (hlc : ∀ i, SmoothLogConcave (F i))
    (hmon : ∀ i, (F i (Set.Ioi 0) ≠ 0 → FiniteMonopolyPrice (positiveBranch (F i))) ∧
      (F i (Set.Iio 0) ≠ 0 → FiniteMonopolyPrice (negativeBranch (F i)))) :
    opt (productLaw F) ≤ ENNReal.ofReal (4 * Real.exp 1) * sRevSym (productLaw F) := by sorry


end IndependentInfoPricing.Main.Supplement
