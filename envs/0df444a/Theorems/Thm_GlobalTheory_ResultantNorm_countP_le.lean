-- Prove2me | Theorems.Thm_GlobalTheory_ResultantNorm_countP_le
-- name    : GlobalTheory.ResultantNorm.countP_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:36.301217+00:00
-- url     : https://prove2.me/theorems/3d6b479b-5568-4410-ad81-dba8a26c1e23
-- title:
--   Resultant Norm: count P le
-- statement:
--   The Resultant Norm construction uses the count P le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L117-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L117-L143

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

theorem GlobalTheory.ResultantNorm.countP_le [DecidableEq Ω] (a b : Multiset Ω) (g : Ω → Ω)
    (h : ∀ t : K, ‖(a.map fun x => g x + algebraMap K Ω t).prod‖ =
      ‖(b.map fun x => g x + algebraMap K Ω t).prod‖) :
    b.countP (fun x => g x = 0) ≤ a.countP (fun x => g x = 0) := by sorry
