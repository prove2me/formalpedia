-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_IsRed_congr
-- name    : GlobalTheory.SgGlob.IsRed.congr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:49.658487+00:00
-- url     : https://prove2.me/theorems/1f9cdb58-ab79-4c40-ba17-8937d88e2edd
-- title:
--   Is Red: congr
-- statement:
--   The Is Red construction uses the congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L171-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L171-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E]

theorem GlobalTheory.SgGlob.IsRed.congr {T : E} {Λ : Submodule (𝓞 E) (Fin n → E)} {P : Matrix (Fin n) (Fin (r + 1)) E}
    {x : Lz E m} {al bl : Matrix (Fin m) (Fin n) E} (h : IsRed σ J Jb Λ P x al) (hP : IsFrame σ J T P)
    (hb : ∀ v ∈ perpX σ J P, bl *ᵥ v = al *ᵥ v) : IsRed σ J Jb Λ P x bl := by sorry
