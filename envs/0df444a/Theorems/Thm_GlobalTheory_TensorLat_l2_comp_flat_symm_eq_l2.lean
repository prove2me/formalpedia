-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_l2_comp_flat_symm_eq_l2
-- name    : GlobalTheory.TensorLat.l2_comp_flat_symm_eq_l2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:02.283731+00:00
-- url     : https://prove2.me/theorems/7708b2e4-067f-473f-9fff-c2763892c007
-- title:
--   Tensor Lat: l2 comp flat symm eq l2
-- statement:
--   The Tensor Lat construction uses the l2 comp flat symm eq l2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean#L114-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean#L114-L183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}

theorem GlobalTheory.TensorLat.l2_comp_flat_symm_eq_l2 (X : PT E) (Y : GT (Fin n × Idx X.dim))
    (hY : ∀ γ, flat γ ∈ lat Y.b ↔ ∀ k, γ k ∈ X.L) (q : ℕ) {F : (Fin n → Vsp X.dim) → ℂ}
    (hF : F ∈ X.Sec q n) : Y.l2 q (F ∘ flat.symm) = X.l2 q F := by sorry
