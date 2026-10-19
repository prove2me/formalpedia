-- Prove2me | Theorems.Thm_OAI_AdaptiveReveals_Scheme_badMass_eq_probability
-- name    : OAI.AdaptiveReveals.Scheme.badMass_eq_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:01:19.37217+00:00
-- url     : https://prove2.me/theorems/1072ac75-06ca-4254-b809-8197319be2a7
-- title:
--   Bad mass equals the probability of being declared bad
-- statement:
--   An adaptive revealing scheme has states $s$; each state reveals a finite set of bits under a product law with parameters $p_s$, may visit a vertex, declares it bad or not according to the revealed values, and moves to a child state whose parameters fix the revealed bits. The bad mass of $s$ is the probability that the revealed values are declared bad; "$U$ is hit within $n$ steps" means every vertex of $U$ is visited and declared bad at its first visit. The bad mass of a state $s$ equals the probability, under its parameters, that the restriction of $\omega$ to the revealed bits is declared bad:
--   $$
--   \mathrm{badMass}(s)=\mathbb P_{p_s}\bigl(\mathrm{bad}_s(\omega|_{J_s})\bigr).
--   $$
--
--   The finite sum over revealed values is thus an honest probability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/AdaptiveReveals.lean#L137-L151

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals

open OAI OAI.AdaptiveReveals OAI.AdaptiveReveals.Scheme
universe uF
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]
variable (P : Scheme E V S)

omit [DecidableEq V] in
theorem OAI.AdaptiveReveals.Scheme.badMass_eq_probability (s : S) : P.badMass s =
    (ProductCylinder.law (P.parameter s)).real
      {ω | P.bad s ((P.reveal s).restrict ω) = true} := by sorry
