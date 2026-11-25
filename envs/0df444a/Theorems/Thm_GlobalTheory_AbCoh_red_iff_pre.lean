-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_red_iff_pre
-- name    : GlobalTheory.AbCoh.red_iff_pre
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:05:59.683021+00:00
-- url     : https://prove2.me/theorems/14517341-45dd-5828-8fbd-0e1b00b54549
-- title:
--   Ab Coh: red iff pre
-- statement:
--   The Ab Coh construction uses the red iff pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocyclePullbackIffPreimageAffineHom.lean#L87-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CocyclePullbackIffPreimageAffineHom.lean#L87-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHom
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

theorem GlobalTheory.AbCoh.red_iff_pre : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) [IsAffineHom φ], (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x ↔ ∃ c : Z1 (OPre φ s'), (∀ U V (a : U ⟶ V), c.1 U V a = preα φ s s' V (f U V a)) ∧ GlobalTheory.CatCoh.H1.mk _ c = (preRes φ s').pull1 x) ∧ (∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z ↔ ∃ c : Z2 (OPre φ s'), (∀ U V W (a : U ⟶ V) (b : V ⟶ W), c.1 U V W a b = preα φ s s' W (v U V W a b)) ∧ GlobalTheory.CatCoh.H2.mk _ c = (preRes φ s').pull2 z) ∧ (∀ y, (preRes φ s').pull1 (pullHO1 h y) = (preCoef h).pull1 y) ∧ ∀ y, (preRes φ s').pull2 (pullHO2 h y) = (preCoef h).pull2 y := by sorry
