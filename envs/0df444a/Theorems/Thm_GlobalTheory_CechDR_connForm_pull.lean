-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_connForm_pull
-- name    : GlobalTheory.CechDR.connForm_pull
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:59:41.767798+00:00
-- url     : https://prove2.me/theorems/36566374-4d26-476b-bebd-206febcd9c54
-- title:
--   Cech DR: conn Form pull
-- statement:
--   The Cech DR construction uses the conn Form pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ComparisonMemCechHodgeFiltration.lean#L85-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ComparisonMemCechHodgeFiltration.lean#L85-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsNilDPOfCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_StructureHomApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
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
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open CatCoh Cris
universe v u v' u'
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
variable {B B' : Type} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R' B'] {α : B →+* B'}
  (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (ha : SemiHom σ α)
  {x : Sp B ⟶ X} (hx : x ≫ s = spMap (algebraMap R B))
  {x' : Sp B' ⟶ X'} (hx' : x' ≫ s' = spMap (algebraMap R' B')) (e : spMap α ≫ x = x' ≫ φ)

theorem GlobalTheory.CechDR.connForm_pull (f : Z1 (O (dp0 R) s)) :
    connForm (h.coef.pullbackOneCocycle f) x' hx' =
      ha.m1 (connForm f x hx) + D R' B' (ev f (semiTriv h ha hx hx' e)) := by sorry
