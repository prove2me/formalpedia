-- Prove2me | Theorems.Thm_GlobalTheory_finRep_one_left
-- name    : GlobalTheory.finRep_one_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:56:41.692468+00:00
-- url     : https://prove2.me/theorems/a8738564-8ce0-4829-8563-be27797133af
-- title:
--   Global Theory: fin Rep one left
-- statement:
--   The Global Theory construction uses the fin Rep one left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinRepExistsIsPullbackSpec.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FinRepExistsIsPullbackSpec.lean#L29-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec
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

theorem GlobalTheory.finRep_one_left {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
    {P S : Type} [CommRing P] [Algebra R₀ P] [CommRing S] [Algebra R₀ S] (g : P →ₐ[R₀] S) :
    (1 : sp (R₀ := R₀) S ⟶ G).left =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (1 : sp (R₀ := R₀) P ⟶ G).left := by sorry
