-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_map_affineIsometry_408915f
-- name    : FunctionalInequalities.KLS.LogConcave.map_affineIsometry_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:07:59.640749+00:00
-- url     : https://prove2.me/theorems/504e15a0-1e0d-4267-8996-145d160d6e64
-- title:
--   Log-Concavity Under Affine Isometric Pushforward
-- statement:
--   This proves preservation of compact-set log-concavity under an affine isometric embedding.
--
--   Let $F$ and $E$ be real normed spaces with Borel measurable structures, assume $F$ is complete, and let $\nu$ be a log-concave probability measure on $F$. Let $\mu$ be a probability measure on $E$ and let $f:F\to E$ be an affine isometric embedding. If
--
--   $$\mu=f_\#\nu,$$
--
--   then $\mu$ is log-concave:
--
--   $$\operatorname{LogConcave}(\mu).$$
--
--   The conclusion allows the image of $f$ to be lower-dimensional and requires no density assumption. This provides the affine-isometric transport direction for the library's compact-set definition of log-concavity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean#L64-L95 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Transport`, declaration `FunctionalInequalities.KLS.LogConcave.map_affineIsometry`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.ConditionalProbability
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
open MeasureTheory Set Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
section Transport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem FunctionalInequalities.KLS.LogConcave.map_affineIsometry_408915f [CompleteSpace F]
    (ν : ProbabilityMeasure F) (hν : LogConcave ν)
    (μ : ProbabilityMeasure E) (f : F →ᵃⁱ[ℝ] E)
    (hmap : (μ : Measure E) = (ν : Measure F).map f) :
    LogConcave μ := by sorry
