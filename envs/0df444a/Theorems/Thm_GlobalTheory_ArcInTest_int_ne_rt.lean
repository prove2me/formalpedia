-- Prove2me | Theorems.Thm_GlobalTheory_ArcInTest_int_ne_rt
-- name    : GlobalTheory.ArcInTest.int_ne_rt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:55:38.615404+00:00
-- url     : https://prove2.me/theorems/8f7a2993-4a29-4f32-b677-056622d18e08
-- title:
--   Arc In Test: int ne rt
-- statement:
--   The Arc In Test construction uses the int ne rt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/MemOfPowEqInt.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/MemOfPowEqInt.lean#L30-L36

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

theorem GlobalTheory.ArcInTest.int_ne_rt (c : Coeff l) (r : ℤ) : ((Int.castRingHom c.F r : c.F) : ℂ) ≠ H.rt0 := by sorry
