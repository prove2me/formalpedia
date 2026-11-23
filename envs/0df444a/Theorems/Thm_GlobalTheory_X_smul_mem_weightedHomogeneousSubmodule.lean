-- Prove2me | Theorems.Thm_GlobalTheory_X_smul_mem_weightedHomogeneousSubmodule
-- name    : GlobalTheory.X_smul_mem_weightedHomogeneousSubmodule
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:07.545328+00:00
-- url     : https://prove2.me/theorems/bf9cbaec-907c-4145-9238-015676ab9271
-- title:
--   Global Theory: X smul mem weighted Homogeneous Submodule
-- statement:
--   The Global Theory construction uses the X smul mem weighted Homogeneous Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L689-L695
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L689-L695

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter
open GlobalTheory
open DirectSum Module MvPolynomial
variable (ι k : Type*) [Field k]

theorem GlobalTheory.X_smul_mem_weightedHomogeneousSubmodule (i : ι) (n : ℤ) (m : MvPolynomial ι k)
    (hm : m ∈ weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) n) :
    (MvPolynomial.X i : MvPolynomial ι k) • m ∈
      weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) (n + 1) := by sorry
