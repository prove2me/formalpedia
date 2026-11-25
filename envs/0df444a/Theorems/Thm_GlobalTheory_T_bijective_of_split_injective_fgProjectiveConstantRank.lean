-- Prove2me | Theorems.Thm_GlobalTheory_T_bijective_of_split_injective_fgProjectiveConstantRank
-- name    : GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:46:36.708342+00:00
-- url     : https://prove2.me/theorems/feac5c03-7f06-49fe-a53e-0e52bb6bab19
-- title:
--   T: bijective of split injective fg Projective Constant Rank
-- statement:
--   The T construction uses the bijective of split injective fg Projective Constant Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfSplitInjectiveFgProjectiveConstantRanStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfSplitInjectiveFgProjectiveConstantRanStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfSplitInjectiveFgProjectiveConstantRan
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfSplitInjectiveFgProjectiveConstantRanStatement
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

theorem GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank : ∀ (R : Type) [CommRing R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ), FP R M n → FP R N n → ∀ (f : M →ₗ[R] N) (r : N →ₗ[R] M), (∀ x, r (f x) = x) → Function.Bijective f := by sorry
