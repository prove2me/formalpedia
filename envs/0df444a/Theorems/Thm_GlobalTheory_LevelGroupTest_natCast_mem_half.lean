-- Prove2me | Theorems.Thm_GlobalTheory_LevelGroupTest_natCast_mem_half
-- name    : GlobalTheory.LevelGroupTest.natCast_mem_half
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:31.395364+00:00
-- url     : https://prove2.me/theorems/e95611fb-2b2b-5932-baaf-33d02922f474
-- title:
--   Level Group Test: nat Cast mem half
-- statement:
--   The Level Group Test construction uses the nat Cast mem half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/LevelGroupEqTopOfCoprime.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/LevelGroupEqTopOfCoprime.lean#L13-L16

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_LevelGroupEqTopOfCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevelGroupTest
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem GlobalTheory.LevelGroupTest.natCast_mem_half (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by sorry
