-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_TwoFormSum_sum_sum_eq_lt
-- name    : GlobalTheory.AbCoh.TwoFormSum.sum_sum_eq_lt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:08:40.212874+00:00
-- url     : https://prove2.me/theorems/52dd4ade-359a-43fd-b758-0a64e08bc7f4
-- title:
--   Two Form Sum: sum sum eq lt
-- statement:
--   The Two Form Sum construction uses the sum sum eq lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalTwoFormEqSumWedgeGlobalOneForms.lean#L35-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlobalTwoFormEqSumWedgeGlobalOneForms.lean#L35-L54

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

theorem GlobalTheory.AbCoh.TwoFormSum.sum_sum_eq_lt {M : Type} [AddCommGroup M] {n : ℕ} (g : Fin n → Fin n → M) (hg : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j, (if i < j then g i j + g j i else 0) := by sorry
