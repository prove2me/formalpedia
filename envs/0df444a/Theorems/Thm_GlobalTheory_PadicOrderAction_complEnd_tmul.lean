-- Prove2me | Theorems.Thm_GlobalTheory_PadicOrderAction_complEnd_tmul
-- name    : GlobalTheory.PadicOrderAction.complEnd_tmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:42:22.2839+00:00
-- url     : https://prove2.me/theorems/562fb7ad-b5d7-4966-8194-a798fbefdf7f
-- title:
--   Padic Order Action: compl End tmul
-- statement:
--   The Padic Order Action construction uses the compl End tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicEndApply.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicEndApply.lean#L76-L84

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

theorem GlobalTheory.PadicOrderAction.complEnd_tmul {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    [Fact p.Prime] {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) (c : ℤ_[p]) (a : O₀) (x : torP B p S) :
    (complEnd f p s h (c ⊗ₜ[ℤ] a) x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x := by sorry
