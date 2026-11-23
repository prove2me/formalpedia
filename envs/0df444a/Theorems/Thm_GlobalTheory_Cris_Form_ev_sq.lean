-- Prove2me | Theorems.Thm_GlobalTheory_Cris_Form_ev_sq
-- name    : GlobalTheory.Cris.Form.ev_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:36.516273+00:00
-- url     : https://prove2.me/theorems/6f5a6ae3-dcae-47e8-ad06-917774754ce1
-- title:
--   Form: ev sq
-- statement:
--   The Form construction uses the ev sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L370-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L370-L375

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
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
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {I : Ideal R} {I' : Ideal R'}
  {I'' : Ideal R''} {X X' X'' : Scheme.{0}}
attribute [instance] Thick.ring Thick.alg Thick.ring₀
variable {s : X ⟶ Sp R}

theorem GlobalTheory.Cris.Form.ev_sq (f : Form s) {T₁ T₂ T₃ T₄ : Thick (dp0 R) s}
    (a : T₁ ⟶ T₂) (p : T₂ ⟶ T₄) (q : T₁ ⟶ T₃) (b : T₃ ⟶ T₄) (h₁ : T₁.J = ⊥) (h₂ : T₂.J = ⊥)
    (h : ∀ c, p.φ (a.φ c) = b.φ (q.φ c)) : ev f.1 p = b.φ (ev f.1 q) + ev f.1 b := by sorry
