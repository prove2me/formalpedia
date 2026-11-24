-- Prove2me | Theorems.Thm_GlobalTheory_TorsionReduced_isReduced_of_forall_dualNumber
-- name    : GlobalTheory.TorsionReduced.isReduced_of_forall_dualNumber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:57.870679+00:00
-- url     : https://prove2.me/theorems/a8d3f5ce-5b33-411f-8f79-eb9ff51e42a5
-- title:
--   Torsion Reduced: is Reduced of forall dual Number
-- statement:
--   The Torsion Reduced construction uses the is Reduced of forall dual Number property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsReducedTorsionGeometricFibre.lean#L14-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsReducedTorsionGeometricFibre.lean#L14-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.TorsionReduced

theorem GlobalTheory.TorsionReduced.isReduced_of_forall_dualNumber (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B]
    (h : ∀ (φ : B →ₐ[F] DualNumber F) (b : B), (φ b).snd = 0) : _root_.IsReduced B := by sorry
