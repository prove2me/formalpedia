-- Prove2me | Theorems.Thm_GlobalTheory_ArcInTest_nonempty_int
-- name    : GlobalTheory.ArcInTest.nonempty_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T18:01:05.14833+00:00
-- url     : https://prove2.me/theorems/20b67921-c00e-5386-a507-d8ebe284872a
-- title:
--   Arc In Test: nonempty int
-- statement:
--   The Arc In Test construction uses the nonempty int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/MemOfPowEqInt.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/MemOfPowEqInt.lean#L38-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_MemOfPowEqInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArcInTest
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem GlobalTheory.ArcInTest.nonempty_int (D : Datum H) (c : Coeff l) :
    Nonempty (ArcIn D l (Int.castRingHom c.F) c.F (Int.castRingHom c.F)) := by sorry
