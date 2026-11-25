-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_TwoFormSum_coordPair_nat
-- name    : GlobalTheory.AbCoh.TwoFormSum.coordPair_nat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:55:17.873704+00:00
-- url     : https://prove2.me/theorems/93d8ec12-a94a-42e5-9c31-3ce4c261cbf7
-- title:
--   Two Form Sum: coord Pair nat
-- statement:
--   The Two Form Sum construction uses the coord Pair nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalTwoFormEqSumWedgeGlobalOneForms.lean#L95-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalTwoFormEqSumWedgeGlobalOneForms.lean#L95-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalTwoFormEqSumWedgeGlobalOneForms
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.TwoFormSum
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.AbCoh.TwoFormSum.coordPair_nat {n : ℕ} (Φ : Frame F n) (i j : Fin n) ⦃T T' : C⦄ (φ : T ⟶ T') (x : Om R (F.obj T) 2) :
    coordPair (Φ.δ i T') (Φ.δ j T') (pOm F 2 φ x) = mp F φ (coordPair (Φ.δ i T) (Φ.δ j T) x) := by sorry
