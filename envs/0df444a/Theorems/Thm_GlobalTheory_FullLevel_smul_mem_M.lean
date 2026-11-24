-- Prove2me | Theorems.Thm_GlobalTheory_FullLevel_smul_mem_M
-- name    : GlobalTheory.FullLevel.smul_mem_M
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:33:38.132705+00:00
-- url     : https://prove2.me/theorems/17f1a878-ddfb-40ae-9b77-7346318c4fb5
-- title:
--   Full Level: smul mem M
-- statement:
--   The Full Level construction uses the smul mem M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFullSymplecticLevelStructureOfTateIso.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFullSymplecticLevelStructureOfTateIso.lean#L57-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIso
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
open GlobalTheory GlobalTheory.FullLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.FullLevel.smul_mem_M (l : Level H) {D : Datum H} {c : 𝓞 E} (hc : c ∈ l.Mb) {a : D.La}
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    ∃ y : D.La, c • a = l.M • y := by sorry
