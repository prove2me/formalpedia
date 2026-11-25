-- Prove2me | Theorems.Thm_GlobalTheory_bxFibre_inj
-- name    : GlobalTheory.bxFibre_inj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:54.372327+00:00
-- url     : https://prove2.me/theorems/55a8a833-20fb-4cc9-8462-31c4bef30957
-- title:
--   Global Theory: bx Fibre inj
-- statement:
--   The Global Theory construction uses the bx Fibre inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsFibreProduct.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsFibreProduct.lean#L41-L46

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

theorem GlobalTheory.bxFibre_inj {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] {φ ψ : Γ(Y, U) →+* P}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) : φ = ψ := by sorry
