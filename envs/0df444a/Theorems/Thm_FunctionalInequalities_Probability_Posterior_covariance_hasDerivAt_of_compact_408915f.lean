-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_covariance_hasDerivAt_of_compact_408915f
-- name    : FunctionalInequalities.Probability.Posterior.covariance_hasDerivAt_of_compact_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:07:58.269349+00:00
-- url     : https://prove2.me/theorems/9ce46a7d-c885-46f2-af34-c64bb7668cac
-- title:
--   Derivative of a Tilted Covariance
-- statement:
--   This is the compact-support derivative formula for a tilted covariance.
--
--   Let $\mu$ be a compactly supported probability measure on a topological, measurable, second-countable Borel space. Let $\phi,g,k$ be continuous and let $f$ be measurable and bounded on $\operatorname{supp}\mu$ by some $C\ge0$. Then
--
--   $$\left.\frac{d}{dt}\right|_{t=0}\operatorname{Cov}_{\mu.\operatorname{tilted}(\phi+t g)}(f,k)
--   =\operatorname{Cov}_{\mu.\operatorname{tilted}(\phi)}(f,gk)
--   -\left(\int g\,d\nu\right)\operatorname{Cov}_{\nu}(f,k)
--   -\left(\int k\,d\nu\right)\operatorname{Cov}_{\nu}(f,g),$$
--
--   where $\nu=\mu.\operatorname{tilted}(\phi)$. This provides the covariance derivative needed for second-order posterior calculations.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L202-L260 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactPrior`, declaration `FunctionalInequalities.Probability.Posterior.covariance_hasDerivAt_of_compact`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]

theorem FunctionalInequalities.Probability.Posterior.covariance_hasDerivAt_of_compact_408915f (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g k f : Ω → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hk : Continuous k) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => covariance f k
      ((μ : Measure Ω).tilted (fun x => φ x + t * g x)))
      (covariance f (fun x => g x * k x) ((μ : Measure Ω).tilted φ) -
        (∫ x, g x ∂((μ : Measure Ω).tilted φ)) * covariance f k ((μ : Measure Ω).tilted φ) -
        (∫ x, k x ∂((μ : Measure Ω).tilted φ)) * covariance f g ((μ : Measure Ω).tilted φ)) 0 := by sorry
