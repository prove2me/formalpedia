-- Prove2me | Theorems.Thm_GlobalTheory_LevelPairing_cSep_spec
-- name    : GlobalTheory.LevelPairing.cSep_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:28.675669+00:00
-- url     : https://prove2.me/theorems/dc3d7dce-e518-45bc-881d-fcec837fc933
-- title:
--   Level Pairing: c Sep spec
-- statement:
--   The Level Pairing construction uses the c Sep spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L21-L29

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

theorem GlobalTheory.LevelPairing.cSep_spec (l : Level H) : cSep l ∈ Mfr l ∧ cSep l - 1 ∈ l.Mb := by sorry
