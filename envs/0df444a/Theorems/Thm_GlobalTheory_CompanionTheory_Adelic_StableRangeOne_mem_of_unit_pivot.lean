-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_mem_of_unit_pivot
-- name    : GlobalTheory.CompanionTheory.Adelic.StableRangeOne.mem_of_unit_pivot
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:16:20.931392+00:00
-- url     : https://prove2.me/theorems/fbc6f263-b289-4c81-a1ef-016b0967fb84
-- title:
--   Stable Range One: mem of unit pivot
-- statement:
--   The Stable Range One construction uses the mem of unit pivot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L164-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L164-L226

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

theorem GlobalTheory.CompanionTheory.Adelic.StableRangeOne.mem_of_unit_pivot {s : Finset ι} {k : ι}
    (ih : ∀ A : Matrix ι ι R, IsUnit A.det → Fixed s A → A ∈ elem R ι)
    {A : Matrix ι ι R} (hA : IsUnit A.det) (hF : Fixed (insert k s) A)
    (hk : k ∉ s) (hu : IsUnit (A k k)) : A ∈ elem R ι := by sorry
