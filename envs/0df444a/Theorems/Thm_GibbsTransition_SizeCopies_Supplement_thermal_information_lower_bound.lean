-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_Supplement_thermal_information_lower_bound
-- name    : GibbsTransition.SizeCopies.Supplement.thermal_information_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:42:40.490866+00:00
-- url     : https://prove2.me/theorems/d4d5e65f-a96a-450c-8ca8-84caf9072527
-- title:
--   Theorem 7.1 — Thermal information lower bound
-- statement:
--   Fix positive rational inverse temperature $\beta$, rational $0<\epsilon\le1/16$, and $0<\delta\le1/4$. Use the product instances with zero bulk edge terms, common published field coupling and boundary, and on-site terms $\operatorname{diag}(0,\theta,\theta+1/8)$ at $\theta_0=1/2-2\epsilon$ and $\theta_1=1/2+2\epsilon$. Both are members of the published class. Every almost-surely stopping learner correct on both satisfies
--   $$\mathbb E_{\theta_0}[V]\ge\frac{\log(1/\delta)}{8\beta^2\epsilon^2}.$$
--   The expectation is under the first instance. There is no side cap, restriction to independent measurements, finite expected stopping assumption, or bound on retained quantum memory.
--
--   This per-spin information lower bound also yields the capped-copy lower bound in the fixed-temperature regime.
--
--   Differences from the source:
--   - encoding: expected total spins for the explicit product hard pair → the published experiment with the actual product interactions and ENNReal stopped spin expectation; reason: this admits infinite expected cost and preserves the exact per-instance inequality
--   - generalization: a correct learner on the model class → an almost-surely stopping physical learner correct on the two displayed product instances; reason: the source proof uses only correctness on this pair; every uniformly correct source learner satisfies both hypotheses
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Theorem 7.1, printed p. 16 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Access
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false

namespace GibbsTransition.SizeCopies.Supplement

theorem thermal_information_lower_bound
    (beta epsilon delta : ℚ) (hb : 0 < beta)
    (he : 0 < epsilon) (hemax : epsilon ≤ 1/16) (hd : 0 < delta) (hdmax : delta ≤ 1/4) :
    let u0 := productInteraction (1/2-2*epsilon)
    let u1 := productInteraction (1/2+2*epsilon)
    InClass u0 ∧ InClass u1 ∧
    ∀ (O ι : Type) [MeasurableSpace O] (A : Experiment O ι),
      IsExperiment A → experimentCorrect A u0 beta epsilon delta →
      experimentCorrect A u1 beta epsilon delta →
      ENNReal.ofReal (Real.log (1/(delta : ℝ)) /
        (8*(beta : ℝ)^2*(epsilon : ℝ)^2)) ≤ experimentSpins A u0 beta := by sorry

end GibbsTransition.SizeCopies.Supplement
