-- Prove2me | Theorems.Thm_GlobalTheory_LevelPairing_dvd_EF_of_mem
-- name    : GlobalTheory.LevelPairing.dvd_EF_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:14.46373+00:00
-- url     : https://prove2.me/theorems/747677f3-b10f-4ba2-9d41-cd8f03070c0a
-- title:
--   Level Pairing: dvd EF of mem
-- statement:
--   The Level Pairing construction uses the dvd EF of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L31-L37

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
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
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem GlobalTheory.LevelPairing.dvd_EF_of_mem (x y : Dw.La) {a : 𝓞 E} (ha : a ∈ Ideal.span {(l.M : 𝓞 E)}) :
    (l.M : ℤ) ∣ Dw.EF x (a • y) := by sorry
