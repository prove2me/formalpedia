-- Prove2me | Theorems.Thm_OAI_CriticalZ3_ScaleData_relay_in_frame
-- name    : OAI.CriticalZ3.ScaleData.relay_in_frame
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:39:18.954348+00:00
-- url     : https://prove2.me/theorems/9b107be3-b688-4a5d-a7d3-3b3ae5194a7f
-- title:
--   Relaying between neighbouring blocks costs at most 13η
-- statement:
--   Let scale data with parameters $r,q,\eta$ be given, and let $S$ be a signed symmetry. Suppose a finite lattice graph contains the image under $S$ of the prism $[-10r,30r+1]\times[-10r,10r]^2$ and all its bits have parameter $q$. For $o$ outside that image,
--   $$
--   \mathbb P\bigl(o\leadsto\Lambda_{4r}(S(0))\ \text{and}\ o\not\leadsto\Lambda_{4r}(S((20r+1)e_0))\bigr)\le13\eta .
--   $$
--
--   This is the bound used for one step of the coarse exploration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/RelayProbability.lean#L209-L289

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

open OAI OAI.CriticalZ3 OAI.CriticalZ3.ScaleData
universe uOmega
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical
variable {model : Model} (s : ScaleData model)

theorem OAI.CriticalZ3.ScaleData.relay_in_frame (G : LatticeGraph) (p : model.Bit → Set.Icc (0:ℝ) 1)
    (S : SignedSymmetry) (hG : G.ContainsSet (S.vertex '' LatticeRelay.Prism s.r))
    (hp : model.UniformOn p s.q (S.vertex '' LatticeRelay.Prism s.r))
    (o : G.Node) (ho : o.1 ∉ S.vertex '' LatticeRelay.Prism s.r) :
    (ProductCylinder.law p).real
      {ω | G.Meets model ω o (cube (S.vertex 0) (4*s.r)) ∧
        ¬G.Meets model ω o (cube (S.vertex (LatticeRelay.axisCenter (20*s.r+1))) (4*s.r))}
      ≤ 13*s.η := by sorry
