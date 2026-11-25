-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_fp_ext_prod
-- name    : GlobalTheory.AbCoh.fp_ext_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:12:51.967802+00:00
-- url     : https://prove2.me/theorems/7fac3f1d-6e2a-5a92-b17e-9e0d47288900
-- title:
--   Ab Coh: fp ext prod
-- statement:
--   The Ab Coh construction uses the fp ext prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FgProjectiveConstantRankExtensionAndProd.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FgProjectiveConstantRankExtensionAndProd.lean#L32-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgProjectiveConstantRankExtensionAndProd
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
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.fp_ext_prod : (∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ) (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Injective i → Function.Surjective p → Function.Exact i p → FP R W a → FP R H b → FP R M (a + b)) ∧ ∀ (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W] [AddCommGroup H] [Module R H] (a b : ℕ), FP R W a → FP R H b → FP R (W × H) (a + b) := by sorry
