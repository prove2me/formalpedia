-- Prove2me | Theorems.Thm_GlobalTheory_FormalChartOf_mem_max_iff
-- name    : GlobalTheory.FormalChartOf.mem_max_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:45:24.492256+00:00
-- url     : https://prove2.me/theorems/c1c9390b-f2f2-44c4-bc0a-0333350cfbfc
-- title:
--   Formal Chart Of: mem max iff
-- statement:
--   The Formal Chart Of construction uses the mem max iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalChart.lean#L271-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalChart.lean#L271-L279

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

theorem GlobalTheory.FormalChartOf.mem_max_iff {R K : LAlg R₀} (hK : maximalIdeal (K : Type) = ⊥) (ρ : LHom R K)
    (hρ : IsNilOver ρ) (a : (R : Type)) : a ∈ maximalIdeal (R : Type) ↔ a ∈ RingHom.ker ρ.1 := by sorry
