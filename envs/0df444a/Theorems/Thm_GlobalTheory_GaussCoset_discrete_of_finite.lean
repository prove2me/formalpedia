-- Prove2me | Theorems.Thm_GlobalTheory_GaussCoset_discrete_of_finite
-- name    : GlobalTheory.GaussCoset.discrete_of_finite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:48:35.219993+00:00
-- url     : https://prove2.me/theorems/eb5a10fc-ceae-4dc9-b0b4-bebcc66ec24c
-- title:
--   Gauss Coset: discrete of finite
-- statement:
--   The Gauss Coset construction uses the discrete of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SummableGaussianCoset.lean#L47-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SummableGaussianCoset.lean#L47-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.GaussCoset

theorem GlobalTheory.GaussCoset.discrete_of_finite {V : Type} [NormedAddCommGroup V] (L : AddSubgroup V)
    (h : {v : V | v ∈ L ∧ ‖v‖ ≤ 1}.Finite) : DiscreteTopology L := by sorry
