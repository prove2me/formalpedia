-- Prove2me | Theorems.Thm_GlobalTheory_TorsionHolomorphic_exists_differentiableOn_torsSq
-- name    : GlobalTheory.TorsionHolomorphic.exists_differentiableOn_torsSq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:07.396343+00:00
-- url     : https://prove2.me/theorems/2b1575c4-e9f6-4daa-9267-4474c7385f36
-- title:
--   Torsion Holomorphic: exists differentiable On tors Sq
-- statement:
--   The Torsion Holomorphic construction uses the exists differentiable On tors Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsDifferentiableOnTorsSq.lean#L130-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsDifferentiableOnTorsSq.lean#L130-L174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsDifferentiableOnTorsSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsionHolomorphic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.TorsionHolomorphic.exists_differentiableOn_torsSq :
    ∀ (E Ix : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : E → Matrix Ix Ix ℂ) (W : Set E) (e₀ : E) (t₀ : ℂ), IsOpen W → e₀ ∈ W → (∀ p q, DifferentiableOn ℂ (fun e => D e p q) W) → (∀ e ∈ W, _root_.GlobalTheory.KeyKa.IsCx deg (D e)) → _root_.GlobalTheory.KeyKa.TorsSq deg (D e₀) t₀ → ∃ (W' : Set E) (t : E → ℂ), IsOpen W' ∧ e₀ ∈ W' ∧ W' ⊆ W ∧ DifferentiableOn ℂ t W' ∧ ∀ e ∈ W', _root_.GlobalTheory.KeyKa.TorsSq deg (D e) (t e) := by sorry
