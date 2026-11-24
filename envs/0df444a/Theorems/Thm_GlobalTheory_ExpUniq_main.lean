-- Prove2me | Theorems.Thm_GlobalTheory_ExpUniq_main
-- name    : GlobalTheory.ExpUniq.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:46:27.029227+00:00
-- url     : https://prove2.me/theorems/7b972ff9-32da-4fb1-8f26-95ec33fb67f4
-- title:
--   Exp Uniq: main
-- statement:
--   The Exp Uniq construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntegralExpansionUniqueOfUniformization.lean#L20-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntegralExpansionUniqueOfUniformization.lean#L20-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsPullOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_PGAppEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntegralExpansionUniqueOfUniformization
import Theorems.Thm_GlobalTheory_ExtDiv_main
import Theorems.Thm_GlobalTheory_ThickDiv_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExpUniq
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.ExpUniq.main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (σ : H0 U.LG.L k) (f g : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → (∀ e, U.ExpandsAt e k σ g) → f = g := by sorry
