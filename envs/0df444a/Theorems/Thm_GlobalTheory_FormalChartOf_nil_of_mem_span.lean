-- Prove2me | Theorems.Thm_GlobalTheory_FormalChartOf_nil_of_mem_span
-- name    : GlobalTheory.FormalChartOf.nil_of_mem_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:46:10.075103+00:00
-- url     : https://prove2.me/theorems/47cdbe30-7d31-442a-b2a6-1fd7d2dcbfe4
-- title:
--   Formal Chart Of: nil of mem span
-- statement:
--   The Formal Chart Of construction uses the nil of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalChart.lean#L281-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalChart.lean#L281-L289

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FormalChartOf
variable {R₀ : Type} [CommRing R₀]

theorem GlobalTheory.FormalChartOf.nil_of_mem_span {S : Type} [CommRing S] {g : ℕ} {a b : Fin g → S} (ha : ∀ i, IsNilpotent (a i))
    (hb : ∀ i, IsNilpotent (b i)) {c : S} (hc : c ∈ Ideal.span (Set.range a ∪ Set.range b)) :
    IsNilpotent c := by sorry
