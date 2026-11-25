-- Prove2me | Theorems.Thm_GlobalTheory_PadicOrderAction_padicEnd_apply
-- name    : GlobalTheory.PadicOrderAction.padicEnd_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:44:02.189281+00:00
-- url     : https://prove2.me/theorems/89df8124-4a30-4325-85b7-49dfb1ce38cf
-- title:
--   Padic Order Action: padic End apply
-- statement:
--   The Padic Order Action construction uses the padic End apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicEndApply.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicEndApply.lean#L34-L35

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

theorem GlobalTheory.PadicOrderAction.padicEnd_apply (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (hM : ∀ x : M, p • x = 0)
    (c : ℤ_[p]) (x : M) : padicEnd p M hM c x = (PadicInt.toZMod c).val • x := by sorry
