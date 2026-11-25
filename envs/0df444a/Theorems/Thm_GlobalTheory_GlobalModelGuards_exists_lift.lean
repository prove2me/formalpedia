-- Prove2me | Theorems.Thm_GlobalTheory_GlobalModelGuards_exists_lift
-- name    : GlobalTheory.GlobalModelGuards.exists_lift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:01.083485+00:00
-- url     : https://prove2.me/theorems/9837b671-fa55-5252-ab55-14bcb95801d1
-- title:
--   Global Model Guards: exists lift
-- statement:
--   The Global Model Guards construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L58-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_ExistsGoodLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GlobalModelGuards
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem GlobalTheory.GlobalModelGuards.exists_lift {l : Level H} {Xo : Moduli D l} {c : Coeff l} (W : ValuationSubring ℂ)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (b : 𝓞 c.F →+* c.V W)
    (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ∃ a : Xo.XF c ⟶ pullback Y.s (spMap b), a ≫ pullback.fst _ _ = Y.j := by sorry
