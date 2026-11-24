-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_gq_one
-- name    : GlobalTheory.SgGlob.Inhab.gq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:35.816583+00:00
-- url     : https://prove2.me/theorems/5697f64a-0399-4f78-8c95-b293ff804a89
-- title:
--   Inhab: gq one
-- statement:
--   The Inhab construction uses the gq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L402-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L402-L406

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

theorem GlobalTheory.SgGlob.Inhab.gq_one (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (g : ℕ) (a b : E) :
    Gq (r := 1) σ 1 (1 + 2 * g) !![(g : E) * splitC σ g a b, 0; 0, -1 - (g : E)] =
      ((g : E) ^ 3 * (a * σ a + b * σ b)) ^ 2 := by sorry
