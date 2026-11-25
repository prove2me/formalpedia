-- Prove2me | Theorems.Thm_GlobalTheory_SplitTorus_pointsEquiv_comp
-- name    : GlobalTheory.SplitTorus.pointsEquiv_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:00.814122+00:00
-- url     : https://prove2.me/theorems/89b98c43-ed00-468f-bf9d-332e14d25279
-- title:
--   Split Torus: points Equiv comp
-- statement:
--   The Split Torus construction uses the points Equiv comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean#L172-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean#L172-L176

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
variable {S : Scheme.{u}} {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  {T T' : Over S}

theorem GlobalTheory.SplitTorus.pointsEquiv_comp (h : T' ⟶ T) (g : T ⟶ splitTorus S X) :
    pointsEquiv T' X (h ≫ g) =
      (MonoidHom.toAdditive (Units.map h.left.appTop.hom.toMonoidHom)).comp (pointsEquiv T X g) := by sorry
