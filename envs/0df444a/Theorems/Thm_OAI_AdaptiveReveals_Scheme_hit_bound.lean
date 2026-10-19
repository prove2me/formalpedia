-- Prove2me | Theorems.Thm_OAI_AdaptiveReveals_Scheme_hit_bound
-- name    : OAI.AdaptiveReveals.Scheme.hit_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:59:29.30573+00:00
-- url     : https://prove2.me/theorems/a29b2f22-edef-402a-a219-0937dbff6dcd
-- title:
--   Hitting many bad vertices is exponentially unlikely
-- statement:
--   An adaptive revealing scheme has states $s$; each state reveals a finite set of bits under a product law with parameters $p_s$, may visit a vertex, declares it bad or not according to the revealed values, and moves to a child state whose parameters fix the revealed bits. The bad mass of $s$ is the probability that the revealed values are declared bad; "$U$ is hit within $n$ steps" means every vertex of $U$ is visited and declared bad at its first visit. Let $I$ be an invariant of states preserved by children of positive weight, and suppose every state in $I$ has bad mass at most $f$. Then for every state $s$ in $I$, every $n$ and finite set $U$,
--   $$
--   \mathbb P_{p_s}(U\ \text{is hit within}\ n\ \text{steps})\le f^{|U|} .
--   $$
--
--   Each first visit to a vertex of $U$ costs a factor $f$, whatever happened before.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/AdaptiveReveals.lean#L76-L135

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

theorem OAI.AdaptiveReveals.Scheme.hit_bound (I : S → Prop) (f : ℝ) (hf : 0 ≤ f)
    (hbad : ∀ s, I s → P.badMass s ≤ f)
    (hchild : ∀ s, I s → ∀ a, 0 < P.weight s a → I (P.child s a))
    (n : ℕ) (s : S) (hs : I s) (U : Finset V) :
    (ProductCylinder.law (P.parameter s)).real (P.hit n s U) ≤ f^U.card := by sorry
