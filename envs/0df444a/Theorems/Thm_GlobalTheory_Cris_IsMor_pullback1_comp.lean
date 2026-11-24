-- Prove2me | Theorems.Thm_GlobalTheory_Cris_IsMor_pullback1_comp
-- name    : GlobalTheory.Cris.IsMor.pullback1_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:27.802368+00:00
-- url     : https://prove2.me/theorems/8b9652f8-367f-41b9-a86e-94bd700eea3b
-- title:
--   Is Mor: pullback1 comp
-- statement:
--   The Is Mor construction uses the pullback1 comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L304-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L304-L309

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
variable {γ : DividedPowers I} {γ' : DividedPowers I'} {γ'' : DividedPowers I''}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''}
variable {σ : R →+* R'} {φ : X' ⟶ X}
variable {τ : R' →+* R''} {ψ : X'' ⟶ X'} {ρ : R →+* R''} {χ : X'' ⟶ X}

theorem GlobalTheory.Cris.IsMor.pullback1_comp (h : IsMor γ s γ' s' σ φ) (h' : IsMor γ' s' γ'' s'' τ ψ)
    (h'' : IsMor γ s γ'' s'' ρ χ) (e : ∀ r, τ (σ r) = ρ r) (e' : ψ ≫ φ = χ) (c : H1 γ s) :
    h'.pull1 (h.pull1 c) = h''.pull1 c := by sorry
