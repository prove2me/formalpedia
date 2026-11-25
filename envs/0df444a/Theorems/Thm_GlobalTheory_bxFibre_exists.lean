-- Prove2me | Theorems.Thm_GlobalTheory_bxFibre_exists
-- name    : GlobalTheory.bxFibre_exists
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:42:52.08401+00:00
-- url     : https://prove2.me/theorems/73bb1390-9b2a-42ec-9991-958a08ba9979
-- title:
--   Global Theory: bx Fibre exists
-- statement:
--   The Global Theory construction uses the bx Fibre exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsFibreProduct.lean#L74-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsFibreProduct.lean#L74-L107

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

theorem GlobalTheory.bxFibre_exists {Y : Scheme.{0}} {F P Q R : Type} [CommRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] [IsLocalRing Q] [CommRing R] [IsLocalRing R]
    (p : F →+* P) (q : F →+* Q) (f : P →+* R) [IsLocalHom f] (g : Q →+* R) [IsLocalHom g]
    (hex : ∀ a b, f a = g b → ∃! c, p c = a ∧ q c = b)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t)
    (a : Spec (CommRingCat.of P) ⟶ Y) (b : Spec (CommRingCat.of Q) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f) ≫ a = Spec.map (CommRingCat.ofHom g) ≫ b) :
    ∃ c : Spec (CommRingCat.of F) ⟶ Y, Spec.map (CommRingCat.ofHom p) ≫ c = a ∧
      Spec.map (CommRingCat.ofHom q) ≫ c = b := by sorry
