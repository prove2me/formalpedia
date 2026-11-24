-- Prove2me | Theorems.Thm_GlobalTheory_TorsionReduced_eq_const_of_pow_eq_one
-- name    : GlobalTheory.TorsionReduced.eq_const_of_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:37.024279+00:00
-- url     : https://prove2.me/theorems/065a7e7b-8f6b-4f02-b581-52cd10968f12
-- title:
--   Torsion Reduced: eq const of pow eq one
-- statement:
--   The Torsion Reduced construction uses the eq const of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsReducedTorsionGeometricFibre.lean#L68-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsReducedTorsionGeometricFibre.lean#L68-L86

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
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem GlobalTheory.TorsionReduced.eq_const_of_pow_eq_one {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
    {N : ℕ} (hN : IsUnit (N : R)) (y : specO O (DualNumber R) ⟶ G) (hy : y ^ N = 1) :
    y = ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) ≫ y := by sorry
