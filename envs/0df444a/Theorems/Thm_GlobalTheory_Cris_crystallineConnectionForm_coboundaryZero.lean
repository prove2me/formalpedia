-- Prove2me | Theorems.Thm_GlobalTheory_Cris_crystallineConnectionForm_coboundaryZero
-- name    : GlobalTheory.Cris.crystallineConnectionForm_coboundaryZero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:01.747006+00:00
-- url     : https://prove2.me/theorems/c885877b-27c2-46e2-9eb2-7dc82881ad55
-- title:
--   Cris: crystalline Connection Form coboundary Zero
-- statement:
--   The Cris construction uses the crystalline Connection Form coboundary Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CrystallineConnectionFormCoboundaryZero.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CrystallineConnectionFormCoboundaryZero.lean#L90-L93

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

theorem GlobalTheory.Cris.crystallineConnectionForm_coboundaryZero (g : C0 (O (dp0 R) s)) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    connForm ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩ x hx = D R B (g (Thick.triv B x hx)) := by sorry
