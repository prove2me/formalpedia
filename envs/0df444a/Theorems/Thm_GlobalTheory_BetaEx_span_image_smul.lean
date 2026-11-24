-- Prove2me | Theorems.Thm_GlobalTheory_BetaEx_span_image_smul
-- name    : GlobalTheory.BetaEx.span_image_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:02:06.736025+00:00
-- url     : https://prove2.me/theorems/2e214a5b-6473-468d-a9d6-a6bdae5b82ed
-- title:
--   Beta Ex: span image smul
-- statement:
--   The Beta Ex construction uses the span image smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L302-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L302-L318

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

theorem GlobalTheory.BetaEx.span_image_smul (𝔞 : Ideal (𝓞 E)) (N : Submodule (𝓞 E) E) :
    Submodule.span (𝓞 F) (φ '' ((𝔞 • N : Submodule (𝓞 E) E) : Set E)) =
      Submodule.span (𝓞 F) ((φ.comp (algebraMap (𝓞 E) E)) '' (𝔞 : Set (𝓞 E))) *
        Submodule.span (𝓞 F) (φ '' (N : Set E)) := by sorry
