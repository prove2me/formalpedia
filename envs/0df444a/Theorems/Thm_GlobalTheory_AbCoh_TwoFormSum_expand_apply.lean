-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_TwoFormSum_expand_apply
-- name    : GlobalTheory.AbCoh.TwoFormSum.expand_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:56:06.082367+00:00
-- url     : https://prove2.me/theorems/34bd2c2c-386a-4f8b-9318-9a12eb8a0937
-- title:
--   Two Form Sum: expand apply
-- statement:
--   The Two Form Sum construction uses the expand apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalTwoFormEqSumWedgeGlobalOneForms.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalTwoFormEqSumWedgeGlobalOneForms.lean#L59-L63

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
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem GlobalTheory.AbCoh.TwoFormSum.expand_apply {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R]) (x : Om R B 2) :
    expand w δ x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by sorry
