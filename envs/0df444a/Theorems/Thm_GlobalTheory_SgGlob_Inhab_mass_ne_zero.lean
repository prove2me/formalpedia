-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_mass_ne_zero
-- name    : GlobalTheory.SgGlob.Inhab.mass_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:53.82457+00:00
-- url     : https://prove2.me/theorems/b0f9ceb6-c70b-4e3f-a617-3eedc0b87bc7
-- title:
--   Inhab: mass ne zero
-- statement:
--   The Inhab construction uses the mass ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L163-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L163-L168

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

theorem GlobalTheory.SgGlob.Inhab.mass_ne_zero (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) :
    Mass (r := 0) σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)] ≠ 0 := by sorry
