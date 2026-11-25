-- Prove2me | Theorems.Thm_GlobalTheory_ArcInTest_mem_of_pow_eq_int
-- name    : GlobalTheory.ArcInTest.mem_of_pow_eq_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:56:26.90644+00:00
-- url     : https://prove2.me/theorems/8becade6-cd0a-4964-a80a-d3c171960cf3
-- title:
--   Arc In Test: mem of pow eq int
-- statement:
--   The Arc In Test construction uses the mem of pow eq int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/MemOfPowEqInt.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/MemOfPowEqInt.lean#L12-L19

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

theorem GlobalTheory.ArcInTest.mem_of_pow_eq_int {F : Type} [Field F] (V : ValuationSubring F) (x : F) (n : ℕ) (hn : 0 < n) (m : ℤ)
    (h : x ^ n = m) : x ∈ V := by sorry
