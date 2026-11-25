-- Prove2me | Theorems.Thm_GlobalTheory_TateMatrices_val_natCast_smul
-- name    : GlobalTheory.TateMatrices.val_natCast_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:48:37.617845+00:00
-- url     : https://prove2.me/theorems/6d44f23e-506b-4cea-a6cc-106ae74a502d
-- title:
--   Tate Matrices: val nat Cast smul
-- statement:
--   The Tate Matrices construction uses the val nat Cast smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L98-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.TateMatrices.val_natCast_smul {Γ : Type} [AddCommGroup Γ] (N m : ℕ) (x : Γ) (hx : N • x = 0) :
    (m : ZMod N).val • x = m • x := by sorry
