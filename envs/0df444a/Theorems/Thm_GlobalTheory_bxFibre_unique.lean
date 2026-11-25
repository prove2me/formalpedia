-- Prove2me | Theorems.Thm_GlobalTheory_bxFibre_unique
-- name    : GlobalTheory.bxFibre_unique
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:39:54.270792+00:00
-- url     : https://prove2.me/theorems/0c84c7d0-16d0-5651-b957-78f2de9dfd84
-- title:
--   Global Theory: bx Fibre unique
-- statement:
--   The Global Theory construction uses the bx Fibre unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsFibreProduct.lean#L53-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsFibreProduct.lean#L53-L72

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

theorem GlobalTheory.bxFibre_unique {Y : Scheme.{0}} {F P Q : Type} [CommRing F] [IsLocalRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] (p : F →+* P) [IsLocalHom p] (q : F →+* Q)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t) (c c' : Spec (CommRingCat.of F) ⟶ Y)
    (hp : Spec.map (CommRingCat.ofHom p) ≫ c = Spec.map (CommRingCat.ofHom p) ≫ c')
    (hq : Spec.map (CommRingCat.ofHom q) ≫ c = Spec.map (CommRingCat.ofHom q) ≫ c') :
    c = c' := by sorry
