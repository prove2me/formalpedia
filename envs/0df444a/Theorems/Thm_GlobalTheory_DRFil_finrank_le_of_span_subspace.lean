-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_finrank_le_of_span_subspace
-- name    : GlobalTheory.DRFil.finrank_le_of_span_subspace
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:35:48.838393+00:00
-- url     : https://prove2.me/theorems/b35a2b97-639c-465d-87de-0bc32c308c11
-- title:
--   DRFil: finrank le of span subspace
-- statement:
--   The DRFil construction uses the finrank le of span subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankMulLeFinrankDdROfSpans.lean#L10-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankMulLeFinrankDdROfSpans.lean#L10-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankMulLeFinrankDdROfSpans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

theorem GlobalTheory.DRFil.finrank_le_of_span_subspace {K F M : Type} [Field K] [CommRing F] [Nontrivial F] [Algebra K F]
    [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M] (D : Submodule K M)
    [FiniteDimensional K D] (h : Submodule.span F (D : Set M) = ⊤) :
    finrank F M ≤ finrank K D := by sorry
