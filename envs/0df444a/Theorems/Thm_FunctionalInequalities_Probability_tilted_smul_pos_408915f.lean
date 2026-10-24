-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_tilted_smul_pos_408915f
-- name    : FunctionalInequalities.Probability.tilted_smul_pos_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:20:24.917254+00:00
-- url     : https://prove2.me/theorems/6066dc16-ec94-4780-9013-bf91d23c9124
-- title:
--   Invariance of Normalized Tilts Under Positive Rescaling
-- statement:
--   This statement proves that normalized tilting is unchanged by a positive rescaling of the base measure.
--
--   Let $A$ be a measurable space, let $μ$ be a measure on $A$, let $f:A\to\mathbb R$, and let $c>0$. Using the definition `Measure.tilted`, the normalized tilt of $(\operatorname{ENNReal.ofReal}(c)\,\bullet\,μ)$ equals the normalized tilt of $μ$:
--
--   $$
--   (\operatorname{ENNReal.ofReal}(c)\,\bullet\,μ).\operatorname{tilted}(f)
--   =
--   μ.\operatorname{tilted}(f).
--   $$
--
--   This algebraic invariance isolates the normalization property of tilted measures and does not require probability or finiteness assumptions on $μ$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Transport.lean#L54-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Transport`, declaration `FunctionalInequalities.Probability.tilted_smul_pos`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section TiltTransport
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]

theorem FunctionalInequalities.Probability.tilted_smul_pos_408915f {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ) {c : ℝ} (hc : 0 < c) :
    (ENNReal.ofReal c • μ).tilted f = μ.tilted f := by sorry
