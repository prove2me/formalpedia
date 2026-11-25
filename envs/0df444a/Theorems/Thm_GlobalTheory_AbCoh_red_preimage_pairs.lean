-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_red_preimage_pairs
-- name    : GlobalTheory.AbCoh.red_preimage_pairs
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:33:31.318297+00:00
-- url     : https://prove2.me/theorems/af7ee050-ec4d-4c84-a471-6acd7c2b343c
-- title:
--   Ab Coh: red preimage pairs
-- statement:
--   The Ab Coh construction uses the red preimage pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CohomologyClassPullbackReductionPairs.lean#L53-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CohomologyClassPullbackReductionPairs.lean#L53-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomologyClassPullbackReductionPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.red_preimage_pairs : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' Y Y' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (φ : X' ⟶ X) (χ : Y' ⟶ Y) [IsAffineHom χ] (h : φ ≫ s = s' ≫ spMap σ) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')), ψ' ≫ φ = χ ≫ ψ → IsAffineHom φ → (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x → ∃ c : Z1 (pairFst ψ ⋙ OPre χ q'), (∀ a b (u : a ⟶ b), c.1 a b u = preα χ q q' ((pairFst ψ).obj b) ((pairPull w).α b (f _ _ ((pairPull w).G.map u)))) ∧ GlobalTheory.CatCoh.H1.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 (pullHO1 w' x)) ∧ ∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z → ∃ c : Z2 (pairFst ψ ⋙ OPre χ q'), (∀ a b d (u : a ⟶ b) (u' : b ⟶ d), c.1 a b d u u' = preα χ q q' ((pairFst ψ).obj d) ((pairPull w).α d (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')))) ∧ GlobalTheory.CatCoh.H2.mk _ c = (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 (pullHO2 w' z) := by sorry
