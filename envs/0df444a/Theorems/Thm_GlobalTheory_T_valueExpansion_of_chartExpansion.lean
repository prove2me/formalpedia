-- Prove2me | Theorems.Thm_GlobalTheory_T_valueExpansion_of_chartExpansion
-- name    : GlobalTheory.T.valueExpansion_of_chartExpansion
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:23:45.010826+00:00
-- url     : https://prove2.me/theorems/08cceae2-8919-4ccc-9060-fb8df1f1b804
-- title:
--   T: value Expansion of chart Expansion
-- statement:
--   The T construction uses the value Expansion of chart Expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValueExpansionOfChartExpansionStatement.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValueExpansionOfChartExpansionStatement.lean#L15-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValueExpansionOfChartExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValueExpansionOfChartExpansionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem GlobalTheory.T.valueExpansion_of_chartExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U'.Expands k σ s → U.ExpF (FractionRing R) k t s.s := by sorry
