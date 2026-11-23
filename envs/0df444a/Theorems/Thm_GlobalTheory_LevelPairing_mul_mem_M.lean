-- Prove2me | Theorems.Thm_GlobalTheory_LevelPairing_mul_mem_M
-- name    : GlobalTheory.LevelPairing.mul_mem_M
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:21.529846+00:00
-- url     : https://prove2.me/theorems/da10cf85-a1c4-4482-8146-c85bb099932e
-- title:
--   Level Pairing: mul mem M
-- statement:
--   The Level Pairing construction uses the mul mem M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L39-L40

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

theorem GlobalTheory.LevelPairing.mul_mem_M {a b : 𝓞 E} (ha : a ∈ l.Mb) (hb : b ∈ Mfr l) : a * b ∈ Ideal.span {(l.M : 𝓞 E)} := by sorry
