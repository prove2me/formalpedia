-- Prove2me | Theorems.Thm_GlobalTheory_PadicOrderAction_padic_mul_eq
-- name    : GlobalTheory.PadicOrderAction.padic_mul_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:39:50.840564+00:00
-- url     : https://prove2.me/theorems/4b10fb07-0d67-5e47-a031-5e9bec4bd654
-- title:
--   Padic Order Action: padic mul eq
-- statement:
--   The Padic Order Action construction uses the padic mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicEndApply.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicEndApply.lean#L100-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicEndApply
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
noncomputable section
open GlobalTheory GlobalTheory.PadicOrderAction
variable {R₀ : Type} [CommRing R₀]

theorem GlobalTheory.PadicOrderAction.padic_mul_eq {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (t : ℤ_[p] →+* R) (c : ℤ_[p])
    (i : R) (hi : p • i = 0) : t c * i = (PadicInt.toZMod c).val • i := by sorry
