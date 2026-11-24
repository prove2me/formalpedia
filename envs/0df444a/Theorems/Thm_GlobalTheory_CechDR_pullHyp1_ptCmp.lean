-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_pullHyp1_ptCmp
-- name    : GlobalTheory.CechDR.pullHyp1_ptCmp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:20.623597+00:00
-- url     : https://prove2.me/theorems/f68cd99b-a470-4282-9eaf-1050c72af74d
-- title:
--   Cech DR: pull Hyp1 pt Cmp
-- statement:
--   The Cech DR construction uses the pull Hyp1 pt Cmp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ComparisonMemCechHodgeFiltration.lean#L147-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ComparisonMemCechHodgeFiltration.lean#L147-L165

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
variable {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (x : ∀ T : C, Sp (F.obj T) ⟶ X) (hx : ∀ T, x T ≫ s = spMap (algebraMap R (F.obj T)))
  (hc : ∀ ⦃T T' : C⦄ (a : T ⟶ T'), spMap (mp F a : F.obj T →+* F.obj T') ≫ x T = x T')

theorem GlobalTheory.CechDR.pullHyp1_ptCmp {C' : Type u'} [Category.{v'} C'] {F' : C' ⥤ CommAlgCat.{0} R'}
    (x' : ∀ T : C', Sp (F'.obj T) ⟶ X') (hx' : ∀ T, x' T ≫ s' = spMap (algebraMap R' (F'.obj T)))
    (hc' : ∀ ⦃T T' : C'⦄ (a : T ⟶ T'), spMap (mp F' a : F'.obj T →+* F'.obj T') ≫ x' T = x' T')
    (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (m : CoefMap σ F F')
    (e : ∀ T, spMap (m.α T) ≫ x (m.G.obj T) = x' T ≫ φ) (c : FirstDeRham s) :
    pullHyp1 m (ptCmp x hx hc c) = ptCmp x' hx' hc' (h.pull1 c) := by sorry
