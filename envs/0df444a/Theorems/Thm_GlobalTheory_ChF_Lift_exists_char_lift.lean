-- Prove2me | Theorems.Thm_GlobalTheory_ChF_Lift_exists_char_lift
-- name    : GlobalTheory.ChF.Lift.exists_char_lift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:50:28.320583+00:00
-- url     : https://prove2.me/theorems/66184af6-4d34-4442-afa9-715c4a9152ac
-- title:
--   Lift: exists char lift
-- statement:
--   The Lift construction uses the exists char lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalTorusCharacterLiftToLaw.lean#L127-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalTorusCharacterLiftToLaw.lean#L127-L181

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalSeriesJacobianChainRuleLinearPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIsChOfTorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MultiplicativeFormalGroupLawPowerPTorsionFiniteFStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GmLawCharsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsAddUnitOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsAddCommMonoidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupSeriesSeparatedByTorsionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubSurjectiveOfLinLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalTorusCharacterLiftToLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF GlobalTheory.ChF.Lift

theorem GlobalTheory.ChF.Lift.exists_char_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d r : ℕ) (F : FGLaw O d), FH p F.F → ∀ (J : Fin d → PS O 1 r) (A' : Matrix (Fin r) (Fin d) O), IsHomF (gmF O r) F.F J → A' * lin J = 1 → ∀ i : Fin r, ∃ u : PS O 1 d, IsCh F.F u ∧ (lin J)ᵀ *ᵥ dl u = Pi.single i 1 := by sorry
