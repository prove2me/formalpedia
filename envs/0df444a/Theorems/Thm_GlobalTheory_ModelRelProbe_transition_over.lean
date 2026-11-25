-- Prove2me | Theorems.Thm_GlobalTheory_ModelRelProbe_transition_over
-- name    : GlobalTheory.ModelRelProbe.transition_over
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:29.485544+00:00
-- url     : https://prove2.me/theorems/3374df4e-8216-4ef7-a719-0fe536bdfa10
-- title:
--   Model Rel Probe: transition over
-- statement:
--   The Model Rel Probe construction uses the transition over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/DominatesLiftUnique.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/DominatesLiftUnique.lean#L23-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_DominatesLiftUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ModelRelProbe
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem GlobalTheory.ModelRelProbe.transition_over {l₂ : Level H} {Xo₂ : Moduli D l₂} {c₂ : Coeff l₂} {O O₂ : Type} [CommRing O] [CommRing O₂]
    {β : O →+* c.F} {β₂ : O₂ →+* c₂.F} (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (b : O →+* O₂) (π : Y₂.X ⟶ Y.X)
    (h : IsTransition Y Y₂ b π) [Mono (spMap β)] (σ : c.F →+* c₂.F) (hσ : σ.comp β = β₂.comp b) :
    π ≫ Y.s = Y₂.s ≫ spMap b ∧ ∃ r : Xo₂.XF c₂ ⟶ Xo.XF c, Y₂.j ≫ π = r ≫ Y.j ∧
      r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap σ := by sorry
