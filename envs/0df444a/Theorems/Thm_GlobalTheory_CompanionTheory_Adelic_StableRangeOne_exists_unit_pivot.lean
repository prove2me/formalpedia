-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_exists_unit_pivot
-- name    : GlobalTheory.CompanionTheory.Adelic.StableRangeOne.exists_unit_pivot
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:16:01.533806+00:00
-- url     : https://prove2.me/theorems/b8f5d477-0c78-47fc-82a8-c11047b3e93e
-- title:
--   Stable Range One: exists unit pivot
-- statement:
--   The Stable Range One construction uses the exists unit pivot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L228-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L228-L277

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.StableRangeOne
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.Adelic.StableRangeOne.exists_unit_pivot (hR : ∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b))
    {s : Finset ι} {k : ι} {A : Matrix ι ι R} (hA : IsUnit A.det)
    (hF : Fixed (insert k s) A) (hk : k ∉ s) :
    ∃ w : ι → R, w k = 0 ∧ Fixed (insert k s) (rowOp k w * A) ∧
      IsUnit ((rowOp k w * A) k k) := by sorry
