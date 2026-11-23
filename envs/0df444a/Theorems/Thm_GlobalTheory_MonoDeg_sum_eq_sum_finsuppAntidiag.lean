-- Prove2me | Theorems.Thm_GlobalTheory_MonoDeg_sum_eq_sum_finsuppAntidiag
-- name    : GlobalTheory.MonoDeg.sum_eq_sum_finsuppAntidiag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:59.837226+00:00
-- url     : https://prove2.me/theorems/18e21097-9b8e-4d90-8fc7-0d144609dda8
-- title:
--   Mono Deg: sum eq sum finsupp Antidiag
-- statement:
--   The Mono Deg construction uses the sum eq sum finsupp Antidiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L17-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.MonoDeg.sum_eq_sum_finsuppAntidiag {ι N : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid N] (a : ℕ) (g : (ι →₀ ℕ) → N) :
    ∑ α : MonoDeg ι a, g α.1 = ∑ α ∈ Finset.finsuppAntidiag Finset.univ a, g α := by sorry
