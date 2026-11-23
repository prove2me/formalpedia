-- Prove2me | Theorems.Thm_GlobalTheory_KS_rsT_sum
-- name    : GlobalTheory.KS.rsT_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:46:50.84544+00:00
-- url     : https://prove2.me/theorems/1c243dae-dfef-40e4-af31-21b10b910c79
-- title:
--   KS: rs T sum
-- statement:
--   The KS construction uses the rs T sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LeISupInfPreimage.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LeISupInfPreimage.lean#L39-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {Y Z : Scheme.{0}}

theorem GlobalTheory.KS.rsT_sum {J : Type*} (S : Finset J) {O₀ : Y.Opens} (s : J → Γ(Y, O₀)) (O : Y.Opens) :
    rsT (∑ a ∈ S, s a) O = ∑ a ∈ S, rsT (s a) O := by sorry
