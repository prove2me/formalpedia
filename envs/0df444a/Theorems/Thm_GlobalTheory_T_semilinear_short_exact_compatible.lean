-- Prove2me | Theorems.Thm_GlobalTheory_T_semilinear_short_exact_compatible
-- name    : GlobalTheory.T.semilinear_short_exact_compatible
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:16:23.193822+00:00
-- url     : https://prove2.me/theorems/f58afb4b-e7c8-473c-a5d9-af823fe97c22
-- title:
--   T: semilinear short exact compatible
-- statement:
--   The T construction uses the semilinear short exact compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SemilinearShortExactCompatibleStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SemilinearShortExactCompatibleStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SemilinearShortExactCompatible
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SemilinearShortExactCompatibleStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.semilinear_short_exact_compatible : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (W' M' H' : Type) [AddCommGroup W'] [Module R' W'] [AddCommGroup M'] [Module R' M'] [AddCommGroup H'] [Module R' H'] (i : W →ₗ[R] M) (p : M →ₗ[R] H) (i' : W' →ₗ[R'] M') (p' : M' →ₗ[R'] H') (a : W →ₛₗ[algebraMap R R'] W') (b : M →ₛₗ[algebraMap R R'] M') (c : H →ₛₗ[algebraMap R R'] H'), Function.Surjective p → Function.Exact i p → Function.Injective i' → Function.Exact i' p' → (∀ x, b (i x) = i' (a x)) → (∀ x, p' (b x) = c (p x)) → (∃ e : R' ⊗[R] W ≃ₗ[R'] W', ∀ x, e (1 ⊗ₜ x) = a x) → (∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ x, e (1 ⊗ₜ x) = c x) → ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ x, e (1 ⊗ₜ x) = b x := by sorry
