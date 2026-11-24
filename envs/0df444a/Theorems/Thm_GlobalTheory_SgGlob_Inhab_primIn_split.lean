-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_primIn_split
-- name    : GlobalTheory.SgGlob.Inhab.primIn_split
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:42.86981+00:00
-- url     : https://prove2.me/theorems/cbfc710b-6133-48ab-81e5-df48a3e426a1
-- title:
--   Inhab: prim In split
-- statement:
--   The Inhab construction uses the prim In split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L333-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L333-L377

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

theorem GlobalTheory.SgGlob.Inhab.primIn_split (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {g : ℕ} (hg : g ≠ 0) {a b : 𝓞 E}
    (hab : differentIdeal ℤ (𝓞 E) = Ideal.span {a, b}) :
    PrimIn (pairLat g (splitP E) (splitQ σ g (a : E) (b : E))) (splitLat E) := by sorry
