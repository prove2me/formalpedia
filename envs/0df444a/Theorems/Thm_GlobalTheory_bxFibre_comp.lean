-- Prove2me | Theorems.Thm_GlobalTheory_bxFibre_comp
-- name    : GlobalTheory.bxFibre_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:41:59.12961+00:00
-- url     : https://prove2.me/theorems/b35dbca7-e179-44c5-9b9c-6fcdbe38c851
-- title:
--   Global Theory: bx Fibre comp
-- statement:
--   The Global Theory construction uses the bx Fibre comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsFibreProduct.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsFibreProduct.lean#L34-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsFibreProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.bxFibre_comp {Y : Scheme.{0}} {A P Q : Type} [CommRing A] [CommRing P] [CommRing Q]
    (φ : A →+* P) (f : P →+* Q) (g : Spec (CommRingCat.of A) ⟶ Y) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom φ) ≫ g =
      Spec.map (CommRingCat.ofHom (f.comp φ)) ≫ g := by sorry
