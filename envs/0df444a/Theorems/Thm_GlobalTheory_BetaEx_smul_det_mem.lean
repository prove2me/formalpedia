-- Prove2me | Theorems.Thm_GlobalTheory_BetaEx_smul_det_mem
-- name    : GlobalTheory.BetaEx.smul_det_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:02:47.188478+00:00
-- url     : https://prove2.me/theorems/00636a1b-5391-4633-b378-f0aea7e1c98a
-- title:
--   Beta Ex: smul det mem
-- statement:
--   The Beta Ex construction uses the smul det mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L35-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L35-L76

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
omit [NumberField E]

theorem GlobalTheory.BetaEx.smul_det_mem (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E) (a : 𝓞 E) (ha : a • m ∈ M')
    (w : Matrix (Fin n) (Fin n) E) (hw : ∀ i, w i ∈ M' ⊔ Submodule.span (𝓞 E) {m}) :
    a • w.det ∈ detSpan M' := by sorry
