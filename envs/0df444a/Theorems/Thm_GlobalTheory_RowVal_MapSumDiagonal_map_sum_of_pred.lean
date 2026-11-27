-- Prove2me | Theorems.Thm_GlobalTheory_RowVal_MapSumDiagonal_map_sum_of_pred
-- name    : GlobalTheory.RowVal.MapSumDiagonal.map_sum_of_pred
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:08:27.85508+00:00
-- url     : https://prove2.me/theorems/b1ef1a87-1384-517a-9973-6848f0d1f4ed
-- title:
--   Map Sum Diagonal: map sum of pred
-- statement:
--   The Map Sum Diagonal construction uses the map sum of pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DiagonalSplit.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DiagonalSplit.lean#L16-L25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeBiadditiveSymmAdjointIntegralEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DiagonalSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowVal GlobalTheory.RowVal.MapSumDiagonal

theorem GlobalTheory.RowVal.MapSumDiagonal.map_sum_of_pred {R Q α : Type} [AddCommMonoid R] [AddCommMonoid Q] (P : R → Prop) (f : R → Q)
    (P0 : P 0) (Padd : ∀ a b, P a → P b → P (a + b)) (f0 : f 0 = 0)
    (fadd : ∀ a b, P a → P b → f (a + b) = f a + f b) (s : Finset α) (a : α → R) (ha : ∀ i, P (a i)) :
    P (∑ i ∈ s, a i) ∧ f (∑ i ∈ s, a i) = ∑ i ∈ s, f (a i) := by sorry
