-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_genConf_one
-- name    : GlobalTheory.SgGlob.Inhab.mem_genConf_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:45.818742+00:00
-- url     : https://prove2.me/theorems/0d235073-3a95-4f10-a868-85559bc6cebe
-- title:
--   Inhab: mem gen Conf one
-- statement:
--   The Inhab construction uses the mem gen Conf one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L379-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L379-L399

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

theorem GlobalTheory.SgGlob.Inhab.mem_genConf_one (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {g : ℕ} (hg : g ≠ 0) {a b : 𝓞 E}
    (hab : differentIdeal ℤ (𝓞 E) = Ideal.span {a, b}) :
    ((splitLat E, splitP E, splitQ σ g (a : E) (b : E)) : Tri E 8 1) ∈
      GenConf σ (splitJ E) 1 (1 + 2 * g) g
        !![(g : E) * splitC σ g (a : E) (b : E), 0; 0, -1 - (g : E)] := by sorry
