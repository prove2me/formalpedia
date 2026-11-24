-- Prove2me | Theorems.Thm_GlobalTheory_ResultantNorm_norm_prod_add
-- name    : GlobalTheory.ResultantNorm.norm_prod_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:21:32.400606+00:00
-- url     : https://prove2.me/theorems/9d72d33b-16cd-41f5-977a-07ea21df50d1
-- title:
--   Resultant Norm: norm prod add
-- statement:
--   The Resultant Norm construction uses the norm prod add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L100-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L100-L115

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.ResultantNorm
open Polynomial Filter Topology
variable {K Ω : Type} [NontriviallyNormedField K] [NormedField Ω] [NormedAlgebra K Ω]

theorem GlobalTheory.ResultantNorm.norm_prod_add [DecidableEq Ω] (a : Multiset Ω) (g : Ω → Ω) (t : K) :
    ‖(a.map fun x => g x + algebraMap K Ω t).prod‖ =
      ‖t‖ ^ a.countP (fun x => g x = 0) *
        ‖((a.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ := by sorry
