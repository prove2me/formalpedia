-- Prove2me | Theorems.Thm_OAI_Problem336AdditiveD139_finite_positive_contraction_dpp_is_strongly_rayleigh
-- name    : OAI.Problem336AdditiveD139.finite_positive_contraction_dpp_is_strongly_rayleigh
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:08.190091+00:00
-- url     : https://prove2.me/theorems/ab8a0adf-5dee-4d1f-ac0c-eae634cd059d
-- statement:
--   The theorem states that, for every nonempty finite index type F and every complex matrix K indexed by F that is a finite positive contraction (K is Hermitian, K i j = conj(K j i), and for every complex vector c the quadratic form Σ conj(c_i) K_ij c_j has real part between 0 and Σ|c_i|², so 0 ≤ K ≤ I in the real-part sense), two things hold. First, there exists a probability measure μ on the finite cube F → Bool (subsets of F) that is a determinantal law for K, meaning that for every subset A of F the probability that all coordinates in A are true equals the determinant of the submatrix of K with rows and columns in A. Second, every probability measure μ on F → Bool that is a determinantal law for K is strongly Rayleigh, meaning that its generating polynomial Σ_x μ({x}) Π_{i : x_i = true} z_i, with the other coordinates contributing factor 1, is nonzero whenever every z_i has strictly positive imaginary part. The statement is recorded as an admitted theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StronglyRayleighDPP.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StronglyRayleighDPP.lean; bytes 5988..6383
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_StronglyRayleighDPP

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12

universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139

theorem finite_positive_contraction_dpp_is_strongly_rayleigh :
    ∀ (F : Type u_3) [Fintype F] [Nonempty F] (K : F → F → ℂ),
      PositiveContractionFinite K →
        (∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K) ∧
          ∀ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K →
            StronglyRayleighFinite μ := by
  sorry

end Problem336AdditiveD139
end
end OAI
