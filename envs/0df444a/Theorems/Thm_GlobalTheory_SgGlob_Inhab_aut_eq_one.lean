-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_aut_eq_one
-- name    : GlobalTheory.SgGlob.Inhab.aut_eq_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:06.696582+00:00
-- url     : https://prove2.me/theorems/1819e3b0-9e16-4194-88e4-1285017170b0
-- title:
--   Inhab: aut eq one
-- statement:
--   The Inhab construction uses the aut eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L117-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L117-L152

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

theorem GlobalTheory.SgGlob.Inhab.aut_eq_one (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) {x : Tri E 2 0}
    (hx : x ∈ GenConf σ !![1, 0; 0, -1] 1 (1 + 2 * g) g !![-1 - (g : E)])
    {γ : Matrix (Fin 2) (Fin 2) E} (hγ : IsoTri σ !![1, 0; 0, -1] γ x x) : γ = 1 := by sorry
