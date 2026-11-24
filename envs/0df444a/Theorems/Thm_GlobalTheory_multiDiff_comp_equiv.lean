-- Prove2me | Theorems.Thm_GlobalTheory_multiDiff_comp_equiv
-- name    : GlobalTheory.multiDiff_comp_equiv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:11.089133+00:00
-- url     : https://prove2.me/theorems/e9acbddd-873b-4746-974f-895ae390d22b
-- title:
--   Global Theory: multi Diff comp equiv
-- statement:
--   The Global Theory construction uses the multi Diff comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L105-L108

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

theorem GlobalTheory.multiDiff_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (g : ι → G)
    (φ : G → M) : multiDiff (g ∘ e) φ = multiDiff g φ := by sorry
