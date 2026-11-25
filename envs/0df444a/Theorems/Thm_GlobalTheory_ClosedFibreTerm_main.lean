-- Prove2me | Theorems.Thm_GlobalTheory_ClosedFibreTerm_main
-- name    : GlobalTheory.ClosedFibreTerm.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:46:13.833643+00:00
-- url     : https://prove2.me/theorems/3aeacc1c-dcbb-474d-9ffe-226f587e4197
-- title:
--   Closed Fibre Term: main
-- statement:
--   The Closed Fibre Term construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/VanishOfTermsVanish.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/VanishOfTermsVanish.lean#L35-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_PGAppEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_VanishOfTermsVanish
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
open GlobalTheory GlobalTheory.ClosedFibreTerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.ClosedFibreTerm.main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (σ : H0 U.LG.L 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), U.ExpandsAt 0 1 σ g → (∀ χ, χ ≠ 0 → ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom ϖ (g χ) g') → ((∃ j, ((fstG (maximalIdeal V) 0 G).left.app _).hom (σ.f j) ≠ 0) ↔ ¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ (g 0) g') := by sorry
