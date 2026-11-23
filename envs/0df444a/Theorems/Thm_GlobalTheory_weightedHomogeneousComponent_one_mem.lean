-- Prove2me | Theorems.Thm_GlobalTheory_weightedHomogeneousComponent_one_mem
-- name    : GlobalTheory.weightedHomogeneousComponent_one_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:12.150452+00:00
-- url     : https://prove2.me/theorems/b31830f5-849f-4b56-9f06-6cad47538022
-- title:
--   Global Theory: weighted Homogeneous Component one mem
-- statement:
--   The Global Theory construction uses the weighted Homogeneous Component one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L105-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingCoeffNonnegOfEventuallyEvalNat.lean#L105-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
open MvPolynomial DirectSum
variable {ι k : Type*} [Field k]

theorem GlobalTheory.weightedHomogeneousComponent_one_mem {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) (n : ℤ) {p : MvPolynomial ι k}
    (hp : p ∈ I) : weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) n p ∈ I := by sorry
