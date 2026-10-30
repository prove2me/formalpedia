-- Prove2me | Theorems.Thm_KuhnWass2019_Reformulation_strong_duality_as_printed
-- name    : KuhnWass2019.Reformulation.strong_duality_as_printed
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T03:15:36.679064+00:00
-- url     : https://prove2.me/theorems/fd2f1caf-0f32-4ca5-a492-8d338daa4f76
-- title:
--   Theorem 7 — strong duality as printed, including zero radius
-- statement:
--   Let $\Xi$ be closed, let $P_N$ be an arbitrary Borel probability law supported on $\Xi$, let $p\ge1$ be finite and let $\varepsilon\ge0$. Suppose the extended loss $\ell$ is measurable, upper semicontinuous and nominally absolutely integrable. The printed theorem asserts
--   $$R_{\varepsilon,p}(P_N,\ell)=\inf_{\gamma\ge0}\left\{E_{P_N}[\ell_\gamma]+\gamma\varepsilon^p\right\},\qquad \ell_\gamma(x)=\sup_{z\in\Xi}\{\ell(z)-\gamma\|z-x\|^p\}.$$
--   This is equality of extended values, without a growth assumption or dual attainment. The zero-radius claim is retained exactly as printed; insight I1 records its counterexample.
--
--   Differences from the source:
--   - encoding: real finite-dimensional vector space with an arbitrary norm → finite-dimensional real normed space with its Borel sigma-algebra and continuous linear functionals as dual vectors; reason: a choice of basis identifies every such space with R^m equipped with the transported norm; the operator norm is the source dual norm
--   - encoding: extended losses, extended expectations and constrained extrema → EReal extrema and the positive-part-first extended expectation; nominal absolute integrability is a lower integral of positive plus negative parts; reason: preserves both infinities, all distributions, and the printed infinity-minus-infinity convention
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen and Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2 (4 Nov 2024), p. 10, Theorem 7, equation (10)

import Mathlib
import Definitions.Def_KuhnWass2019_Reformulation_RegularLoss
import Definitions.Def_KuhnWass2019_Reformulation_worstCaseRisk
import Definitions.Def_KuhnWass2019_Reformulation_moreauYosida

open MeasureTheory
open scoped ENNReal Classical

namespace KuhnWass2019.Reformulation

/-- Theorem 7, arXiv:1908.08729v2, p. 10, as printed, including zero radius. -/
theorem strong_duality_as_printed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 1 ≤ p) (Ξ : Set E) (hΞ : IsClosed Ξ)
    (PN : Measure E) [IsProbabilityMeasure PN] (hPN : PN Ξᶜ = 0)
    (ℓ : E → EReal) (hℓ : RegularLoss PN ℓ) :
    worstCaseRisk ε p Ξ PN ℓ =
      ⨅ (γ : ℝ) (_ : 0 ≤ γ),
        DupacovaWets.Consistency.expect PN (moreauYosida Ξ ℓ p γ)
          + ((γ * ε ^ p : ℝ) : EReal) := by sorry

end KuhnWass2019.Reformulation
