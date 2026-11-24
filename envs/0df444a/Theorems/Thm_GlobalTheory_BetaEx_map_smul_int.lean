-- Prove2me | Theorems.Thm_GlobalTheory_BetaEx_map_smul_int
-- name    : GlobalTheory.BetaEx.map_smul_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:02:46.882507+00:00
-- url     : https://prove2.me/theorems/753c6bc8-2178-4599-9726-715cfbe7ef15
-- title:
--   Beta Ex: map smul int
-- statement:
--   The Beta Ex construction uses the map smul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L288-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L288-L290

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
variable {E F : Type} [Field E] [Field F] (φ : E →+* F)

theorem GlobalTheory.BetaEx.map_smul_int (b : 𝓞 E) (x : E) : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by sorry
