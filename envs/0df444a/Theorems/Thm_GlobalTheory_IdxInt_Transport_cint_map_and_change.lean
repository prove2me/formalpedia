-- Prove2me | Theorems.Thm_GlobalTheory_IdxInt_Transport_cint_map_and_change
-- name    : GlobalTheory.IdxInt.Transport.cint_map_and_change
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:39:51.264883+00:00
-- url     : https://prove2.me/theorems/aa34ac87-ce1e-4bbe-8e11-62837a032db1
-- title:
--   Transport: cint map and change
-- statement:
--   The Transport construction uses the cint map and change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralTransportAndChange.lean#L151-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralTransportAndChange.lean#L151-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralTransportAndChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Transport
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']
open scoped Pointwise Classical
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']

theorem GlobalTheory.IdxInt.Transport.cint_map_and_change : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'], (∀ (e : W ≃+ W') (A : AddSubgroup W) (φ : W' → ℂ), (_root_.GlobalTheory.IdxInt.Nice (A.map e.toAddMonoidHom) φ ↔ _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w))) ∧ _root_.GlobalTheory.IdxInt.cint (A.map e.toAddMonoidHom) φ = _root_.GlobalTheory.IdxInt.cint A (fun w => φ (e w))) ∧ ∀ (A A' : AddSubgroup W) (φ : W → ℂ), A.relIndex A' ≠ 0 → A'.relIndex A ≠ 0 → (_root_.GlobalTheory.IdxInt.Nice A φ ↔ _root_.GlobalTheory.IdxInt.Nice A' φ) ∧ _root_.GlobalTheory.IdxInt.cint A' φ * (A.relIndex A' : ℂ) = _root_.GlobalTheory.IdxInt.cint A φ * (A'.relIndex A : ℂ) := by sorry
