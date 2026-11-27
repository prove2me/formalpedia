-- Prove2me | Theorems.Thm_GlobalTheory_multiDiff_add
-- name    : GlobalTheory.multiDiff_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:16.997202+00:00
-- url     : https://prove2.me/theorems/419e6f6b-708f-5bcb-89e3-7d9c955f2b6f
-- title:
--   Global Theory: multi Diff add
-- statement:
--   The Global Theory construction uses the multi Diff add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L110-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

theorem GlobalTheory.multiDiff_add {ι : Type*} [Fintype ι] (g : ι → G) (φ ψ : G → M) :
    multiDiff g (φ + ψ) = multiDiff g φ + multiDiff g ψ := by sorry
