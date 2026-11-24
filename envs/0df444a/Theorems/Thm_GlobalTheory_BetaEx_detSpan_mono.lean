-- Prove2me | Theorems.Thm_GlobalTheory_BetaEx_detSpan_mono
-- name    : GlobalTheory.BetaEx.detSpan_mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:59:40.067514+00:00
-- url     : https://prove2.me/theorems/3ba6b971-1300-48af-999f-e448acfe4941
-- title:
--   Beta Ex: det Span mono
-- statement:
--   The Beta Ex construction uses the det Span mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L88-L91

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

theorem GlobalTheory.BetaEx.detSpan_mono {M' M : Submodule (𝓞 E) (Fin n → E)} (h : M' ≤ M) : detSpan M' ≤ detSpan M := by sorry
