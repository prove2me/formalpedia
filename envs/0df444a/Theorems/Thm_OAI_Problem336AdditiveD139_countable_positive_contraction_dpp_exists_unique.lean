-- Prove2me | Theorems.Thm_OAI_Problem336AdditiveD139_countable_positive_contraction_dpp_exists_unique
-- name    : OAI.Problem336AdditiveD139.countable_positive_contraction_dpp_exists_unique
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:08.062177+00:00
-- url     : https://prove2.me/theorems/a83aa001-441b-485f-b9ea-774881e1d1fd
-- statement:
--   The theorem states that for every countable index set I and every complex kernel K : I × I → ℂ that is a positive contraction kernel, there exists exactly one probability measure μ on the space of Boolean configurations I → Bool (with its product structure) that is a determinantal law for K. Here K is a positive contraction kernel when it is Hermitian, K(i,j) equals the complex conjugate of K(j,i), and for every finite subset S of I and every complex vector c on S, the real part of the quadratic form Σ_{i,j∈S} conj(c_i) K(i,j) c_j lies between 0 and Σ_{i∈S} |c_i|². The measure μ is a determinantal law for K when, for every finite subset A of I, the μ-probability that x_i = true for all i in A, viewed as a complex number, equals the determinant of the A × A matrix of entries K(i,j). Thus the finite-dimensional joint inclusion probabilities of such a process are prescribed by these determinants, and the statement asserts both existence and uniqueness of the resulting measure.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StronglyRayleighDPP.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StronglyRayleighDPP.lean; bytes 6385..6630
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

theorem countable_positive_contraction_dpp_exists_unique :
    ∀ (I : Type u_4) [Countable I] (K : I → I → ℂ),
      PositiveContractionKernel K →
        ∃! μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K := by
  sorry

end Problem336AdditiveD139
end
end OAI
