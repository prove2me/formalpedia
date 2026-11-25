-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_IsoRig_inv
-- name    : GlobalTheory.SgGlob.IsoRig.inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:53.62686+00:00
-- url     : https://prove2.me/theorems/f8dbff06-225a-5868-9b12-d835f62aa2a7
-- title:
--   Iso Rig: inv
-- statement:
--   The Iso Rig construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L282-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L282-L293

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

theorem GlobalTheory.SgGlob.IsoRig.inv (hJ : IsUnit J.det) {γ : Matrix (Fin n) (Fin n) E} {c d : Rig E n m r}
    (h : IsoRig σ J γ c d) : IsoRig σ J γ⁻¹ d c := by sorry
