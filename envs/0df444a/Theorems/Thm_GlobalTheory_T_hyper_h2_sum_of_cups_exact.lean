-- Prove2me | Theorems.Thm_GlobalTheory_T_hyper_h2_sum_of_cups_exact
-- name    : GlobalTheory.T.hyper_h2_sum_of_cups_exact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:53:01.841013+00:00
-- url     : https://prove2.me/theorems/ee77e1cf-b927-53c6-9009-35b68fe025e5
-- title:
--   T: hyper h2 sum of cups exact
-- statement:
--   The T construction uses the hyper h2 sum of cups exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2SumOfCupsExactStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HyperH2SumOfCupsExactStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2SumOfCupsExact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2SumOfCupsExactStatement
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO

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

theorem GlobalTheory.T.hyper_h2_sum_of_cups_exact : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ c : cechDeRhamTotalCocyclesTwo F, (∃ f, d1 F f = c.1.1) → ∃ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), Hyp2.mk F c = ∑ k, cupHyp F (a k) (clAll F hc (w k)) := by sorry
