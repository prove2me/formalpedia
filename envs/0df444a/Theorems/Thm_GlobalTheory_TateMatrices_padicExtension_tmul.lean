-- Prove2me | Theorems.Thm_GlobalTheory_TateMatrices_padicExtension_tmul
-- name    : GlobalTheory.TateMatrices.padicExtension_tmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:50:53.971558+00:00
-- url     : https://prove2.me/theorems/712851e3-6eb4-5dc1-afff-1ddfb46c1fd7
-- title:
--   Tate Matrices: padic Extension tmul
-- statement:
--   The Tate Matrices construction uses the padic Extension tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L219-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean#L219-L222

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
variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {B : BX R₀} {O : LAlg R₀}
  {O₀ : Type} [CommRing O₀]

theorem GlobalTheory.TateMatrices.padicExtension_tmul {κ : Type} [Fintype κ] [DecidableEq κ] (ρ : O₀ →+* Matrix κ κ ℤ_[p])
    (c : ℤ_[p]) (a : O₀) : padicExtension ρ (c ⊗ₜ[ℤ] a) = c • ρ a := by sorry
