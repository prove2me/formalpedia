-- Prove2me | Theorems.Thm_GlobalTheory_ArcInTest_rank_le
-- name    : GlobalTheory.ArcInTest.rank_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:57:41.975914+00:00
-- url     : https://prove2.me/theorems/a27493e9-9e02-47b1-8a6b-a9522c2d44cd
-- title:
--   Arc In Test: rank le
-- statement:
--   The Arc In Test construction uses the rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/MemOfPowEqInt.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/MemOfPowEqInt.lean#L58-L64

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

theorem GlobalTheory.ArcInTest.rank_le {D : Datum H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) (r z : O) (hr : ((β r : c.F) : ℂ) = H.rt0)
    (hz : ((β z : c.F) : ℂ) = zeta l.A) (τ : 𝓞 E →+* AlgebraicClosure (FractionRing O')) :
    Module.finrank (𝓞 E) a.D₀.X ≤ max D.p D.q := by sorry
