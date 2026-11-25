-- Prove2me | Theorems.Thm_GlobalTheory_SkewLat_mem_pairLat
-- name    : GlobalTheory.SkewLat.mem_pairLat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:38.698812+00:00
-- url     : https://prove2.me/theorems/d53ed34e-8ccd-5a2b-a184-ceff9be283e1
-- title:
--   Skew Lat: mem pair Lat
-- statement:
--   The Skew Lat construction uses the mem pair Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemPairLat.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemPairLat.lean#L31-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemPairLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SkewLat
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.SkewLat.mem_pairLat {a b d : ℕ} {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}
    {e : Fin a ⊕ Fin b ≃ Fin d} {x : Fin d → E} :
    x ∈ pairLat ΛA ΛB e ↔ (fun k => x (e (.inl k))) ∈ ΛA ∧ (fun k => x (e (.inr k))) ∈ ΛB := by sorry
