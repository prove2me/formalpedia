-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_IsoRig_mul
-- name    : GlobalTheory.SgGlob.IsoRig.mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:23.866457+00:00
-- url     : https://prove2.me/theorems/f94fc769-c9f4-4d09-9e56-8d999305bfd3
-- title:
--   Iso Rig: mul
-- statement:
--   The Iso Rig construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L273-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L273-L280

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

theorem GlobalTheory.SgGlob.IsoRig.mul {γ δ : Matrix (Fin n) (Fin n) E} {c d e : Rig E n m r} (h : IsoRig σ J γ c d)
    (k : IsoRig σ J δ d e) : IsoRig σ J (δ * γ) c e := by sorry
