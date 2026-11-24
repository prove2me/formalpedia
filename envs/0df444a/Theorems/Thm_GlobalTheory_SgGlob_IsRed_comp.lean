-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_IsRed_comp
-- name    : GlobalTheory.SgGlob.IsRed.comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:26.057803+00:00
-- url     : https://prove2.me/theorems/beb53a65-fde1-4342-9b70-1e7f2282c456
-- title:
--   Is Red: comp
-- statement:
--   The Is Red construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L213-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L213-L227

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

theorem GlobalTheory.SgGlob.IsRed.comp {Λ : Submodule (𝓞 E) (Fin n → E)} {P : Matrix (Fin n) (Fin (r + 1)) E} {x y : Lz E m}
    {al : Matrix (Fin m) (Fin n) E} (h : IsRed σ J Jb Λ P x al) (hJ : IsUnit Jb.det)
    {γ : Matrix (Fin m) (Fin m) E} (hγ : IsoLz σ Jb γ x y) : IsRed σ J Jb Λ P y (γ * al) := by sorry
