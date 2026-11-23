-- Prove2me | Theorems.Thm_GlobalTheory_mem_smul_of_isHomogeneous_of_coeff_mem
-- name    : GlobalTheory.mem_smul_of_isHomogeneous_of_coeff_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:20.370321+00:00
-- url     : https://prove2.me/theorems/d42b8232-4765-412d-ba94-386072e000c0
-- title:
--   Global Theory: mem smul of is Homogeneous of coeff mem
-- statement:
--   The Global Theory construction uses the mem smul of is Homogeneous of coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFormsAlgebraicIndependentSmulSubSumMem.lean#L39-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ ι R : Type*} [CommRing R]

theorem GlobalTheory.mem_smul_of_isHomogeneous_of_coeff_mem {J : Ideal R} {Q : Submodule R (MvPolynomial σ R)}
    {n : ℕ} (hQ : ∀ m : σ →₀ ℕ, m.degree = n → monomial m (1 : R) ∈ Q) {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous n) (hJ : ∀ m, p.coeff m ∈ J) : p ∈ J • Q := by sorry
