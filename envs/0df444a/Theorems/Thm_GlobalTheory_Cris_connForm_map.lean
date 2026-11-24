-- Prove2me | Theorems.Thm_GlobalTheory_Cris_connForm_map
-- name    : GlobalTheory.Cris.connForm_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:28:40.183255+00:00
-- url     : https://prove2.me/theorems/bc6979a2-d987-424b-8ff4-9cd1d85592eb
-- title:
--   Cris: conn Form map
-- statement:
--   The Cris construction uses the conn Form map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CrystallineConnectionFormCoboundaryZero.lean#L95-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CrystallineConnectionFormCoboundaryZero.lean#L95-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
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
variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
open KaehlerDifferential
variable (R) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
attribute [local instance] opModule
attribute [local instance] isCentralScalar_kaehler isScalarTower_kaehler
variable {R B B'} {s : X ⟶ Sp R}

theorem GlobalTheory.Cris.connForm_map [Algebra B B'] [IsScalarTower R B B'] (f : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) (x' : Sp B' ⟶ X) (hx' : x' ≫ s = spMap (algebraMap R B'))
    (e : spMap (algebraMap B B') ≫ x = x') :
    connForm f x' hx' - KaehlerDifferential.map R R B B' (connForm f x hx) =
      D R B' (ev f (Thick.trivHom (hx := hx) (T := Thick.triv B' x' hx')
        (IsScalarTower.toAlgHom R B B') e)) := by sorry
