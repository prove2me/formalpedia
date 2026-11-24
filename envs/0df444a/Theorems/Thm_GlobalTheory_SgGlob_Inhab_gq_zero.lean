-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_gq_zero
-- name    : GlobalTheory.SgGlob.Inhab.gq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:36.940069+00:00
-- url     : https://prove2.me/theorems/95928e16-0641-48aa-9d65-4853322b8a27
-- title:
--   Inhab: gq zero
-- statement:
--   The Inhab construction uses the gq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L96-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
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
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]

theorem GlobalTheory.SgGlob.Inhab.gq_zero (σ : E →+* E) (g : ℕ) :
    Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] = (g : E) ^ 2 := by sorry
