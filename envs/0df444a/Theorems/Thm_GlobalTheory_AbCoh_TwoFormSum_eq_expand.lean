-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_TwoFormSum_eq_expand
-- name    : GlobalTheory.AbCoh.TwoFormSum.eq_expand
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:09:19.178491+00:00
-- url     : https://prove2.me/theorems/27bfe39a-81e9-4c9c-8757-6cfbe8df6d4f
-- title:
--   Two Form Sum: eq expand
-- statement:
--   The Two Form Sum construction uses the eq expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalTwoFormEqSumWedgeGlobalOneForms.lean#L65-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalTwoFormEqSumWedgeGlobalOneForms.lean#L65-L89

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

theorem GlobalTheory.AbCoh.TwoFormSum.eq_expand {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R])
    (hs : ∀ ω, ω = ∑ i, δ i ω • w i) (x : Om R B 2) :
    x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by sorry
