-- Prove2me | Theorems.Thm_GlobalTheory_PadicOrderAction_complMat_tmul
-- name    : GlobalTheory.PadicOrderAction.complMat_tmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:42:19.113167+00:00
-- url     : https://prove2.me/theorems/492e2b7d-7998-40d9-84f6-84568b475a1b
-- title:
--   Padic Order Action: compl Mat tmul
-- statement:
--   The Padic Order Action construction uses the compl Mat tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicEndApply.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicEndApply.lean#L91-L95

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

theorem GlobalTheory.PadicOrderAction.complMat_tmul {g : ℕ} {O : Type} [CommRing O] {O₀ : Type} [CommRing O₀] (p : ℕ)
    [Fact p.Prime] [Algebra ℤ_[p] O] (dL : O₀ →+* Matrix (Fin g) (Fin g) O) (c : ℤ_[p]) (a : O₀) :
    complMat p dL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c • dL a := by sorry
