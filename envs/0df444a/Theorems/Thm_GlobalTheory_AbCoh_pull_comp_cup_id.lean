-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_pull_comp_cup_id
-- name    : GlobalTheory.AbCoh.pull_comp_cup_id
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:51:38.913611+00:00
-- url     : https://prove2.me/theorems/10f0c4ff-4dec-4096-bf06-6667318d94bb
-- title:
--   Ab Coh: pull comp cup id
-- statement:
--   The Ab Coh construction uses the pull comp cup id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyPullbackCompCupId.lean#L243-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StructureSheafCohomologyPullbackCompCupId.lean#L243-L254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StructureSheafCohomologyPullbackCompCupId
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup

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
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.pull_comp_cup_id : (∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (R'' : Type) [CommRing R''] (X'' : Scheme.{0}) (s'' : X'' ⟶ Sp R'') (τ : R' →+* R'') (ψ : X'' ⟶ X') (h' : ψ ≫ s' = s'' ≫ spMap τ) (ρ : R →+* R'') (χ : X'' ⟶ X) (h'' : χ ≫ s = s'' ≫ spMap ρ), χ = ψ ≫ φ → (∀ r, ρ r = τ (σ r)) → (∀ a, pullHO1 h' (pullHO1 h a) = pullHO1 h'' a) ∧ (∀ a, pullHO2 h' (pullHO2 h a) = pullHO2 h'' a) ∧ (∀ a, GlobalTheory.CechDR.pullForm h' (GlobalTheory.CechDR.pullForm h a) = GlobalTheory.CechDR.pullForm h'' a) ∧ (∀ a, pullHH1 h' (pullHH1 h a) = pullHH1 h'' a) ∧ ∀ a, pullHH2 h' (pullHH2 h a) = pullHH2 h'' a) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ), (∀ a b, pullHO2 h (cup _ a b) = cup _ (pullHO1 h a) (pullHO1 h b)) ∧ (∀ a b, pullHH2 h (cupHH s a b) = cupHH s' (pullHH1 h a) (pullHH1 h b)) ∧ ∀ a, toHO1 s' (pullHH1 h a) = pullHO1 h (toHO1 s a)) ∧ ∀ (R : Type) [CommRing R] (A : Over (Sp R)), (∀ a, pO1 (𝟙 A) a = a) ∧ (∀ a, structureSheafH2Pullback (𝟙 A) a = a) ∧ (∀ a, pF (𝟙 A) a = a) ∧ (∀ a, deRhamH1Pullback (𝟙 A) a = a) ∧ ∀ a, deRhamH2Pullback (𝟙 A) a = a := by sorry
