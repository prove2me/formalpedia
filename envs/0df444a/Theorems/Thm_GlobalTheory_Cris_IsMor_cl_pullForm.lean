-- Prove2me | Theorems.Thm_GlobalTheory_Cris_IsMor_cl_pullForm
-- name    : GlobalTheory.Cris.IsMor.cl_pullForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:41.070799+00:00
-- url     : https://prove2.me/theorems/2156ec26-f23d-453c-99b5-81c4b82b1a56
-- title:
--   Is Mor: cl pull Form
-- statement:
--   The Is Mor construction uses the cl pull Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L415-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L415-L417

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

theorem GlobalTheory.Cris.IsMor.cl_pullForm {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
    (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (f : Form s) :
    Form.cl s' (h.pullForm f) = h.pull1 (Form.cl s f) := by sorry
