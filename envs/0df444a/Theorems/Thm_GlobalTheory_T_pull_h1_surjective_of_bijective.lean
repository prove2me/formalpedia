-- Prove2me | Theorems.Thm_GlobalTheory_T_pull_h1_surjective_of_bijective
-- name    : GlobalTheory.T.pull_h1_surjective_of_bijective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:32.143926+00:00
-- url     : https://prove2.me/theorems/41b3a662-6162-448e-b077-cb7d07e2e57b
-- title:
--   T: pull h1 surjective of bijective
-- statement:
--   The T construction uses the pull h1 surjective of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullH1SurjectiveOfBijectiveStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullH1SurjectiveOfBijectiveStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullH1SurjectiveOfBijective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullH1SurjectiveOfBijectiveStatement
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

theorem GlobalTheory.T.pull_h1_surjective_of_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap σ)), Function.Bijective σ → Function.Surjective (pullHO1 h.w) := by sorry
