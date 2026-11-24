-- Prove2me | Theorems.Thm_GlobalTheory_TangentPow_pow_eq_scale_and_existsUnique_torsion
-- name    : GlobalTheory.TangentPow.pow_eq_scale_and_existsUnique_torsion
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:02:42.447835+00:00
-- url     : https://prove2.me/theorems/7dfa2554-bf4c-44a6-a57c-bb282814ba01
-- title:
--   Tangent Pow: pow eq scale and exists Unique torsion
-- statement:
--   The Tangent Pow construction uses the pow eq scale and exists Unique torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowEqScaleAndExistsUniqueTorsion.lean#L124-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowEqScaleAndExistsUniqueTorsion.lean#L124-L135

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
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
open GlobalTheory GlobalTheory.TangentPow
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]
variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {y : specO O (DualNumber R) ⟶ G}

theorem GlobalTheory.TangentPow.pow_eq_scale_and_existsUnique_torsion :
    ∀ (O : Type) [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] (R : Type)
      [CommRing R] [Algebra O R] (N : ℕ) (y : specO O (DualNumber R) ⟶ G),
      ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1 →
      y ^ N = ptMap ((TrivSqZeroExt.map ((N : R) • (LinearMap.id : R →ₗ[R] R))).restrictScalars O)
          ≫ y ∧
        ((N : R) = 0 → ∃! w : specO O (DualNumber R) ⟶ torsion G N, w ≫ torsion.ι G N = y) := by sorry
