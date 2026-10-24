-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_cond_408915f
-- name    : FunctionalInequalities.KLS.LogConcave.cond_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:18:37.182893+00:00
-- url     : https://prove2.me/theorems/d2a8a32a-72b4-403f-9bfd-9259f275f967
-- title:
--   Log-Concavity Under Convex Conditioning
-- statement:
--   This formalizes the conditioning statement used in the compact-support reduction for Theorem 4.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a real normed space with Borel measurable structure, and let $\mu$ be a log-concave probability measure. Let $C\subseteq E$ be convex and closed, and assume $\mu(C)\ne0$. Form the conditional probability measure $\mu[\mid C]$ using `cond`.
--
--   Then the conditional law remains log-concave:
--
--   $$
--   \operatorname{LogConcave}(\mu[\mid C]).
--   $$
--
--   The result applies the compact-set definition of log-concavity and is particularly suited to conditioning on closed balls. It makes no assertion about isotropy or compactness of the conditional law beyond the stated hypotheses.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean#L212-L360 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Transport`, declaration `FunctionalInequalities.KLS.LogConcave.cond`; the repository is private at upload time).

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
section Conditioning
open ProbabilityTheory

theorem FunctionalInequalities.KLS.LogConcave.cond_408915f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) (hpos : (μ : Measure E) C ≠ 0) :
    LogConcave (⟨(μ : Measure E)[|C], cond_isProbabilityMeasure hpos⟩ : ProbabilityMeasure E) := by sorry
