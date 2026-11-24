-- Prove2me | Theorems.Thm_GlobalTheory_BetaEx_detSpan_cyclic
-- name    : GlobalTheory.BetaEx.detSpan_cyclic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:13.250654+00:00
-- url     : https://prove2.me/theorems/505dca28-9bbd-43f4-8bb4-1222892a9c61
-- title:
--   Beta Ex: det Span cyclic
-- statement:
--   The Beta Ex construction uses the det Span cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L115-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIndexIdeal.lean#L115-L175

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

theorem GlobalTheory.BetaEx.detSpan_cyclic (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E)
    (hb : Bdd (M' ⊔ Submodule.span (𝓞 E) {m})) :
    detSpan M' = (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) •
      detSpan (M' ⊔ Submodule.span (𝓞 E) {m}) := by sorry
