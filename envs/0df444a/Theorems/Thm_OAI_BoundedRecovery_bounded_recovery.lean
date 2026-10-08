-- Prove2me | Theorems.Thm_OAI_BoundedRecovery_bounded_recovery
-- name    : OAI.BoundedRecovery.bounded_recovery
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:24.01846+00:00
-- url     : https://prove2.me/theorems/d0db4841-0763-407e-9c52-3970931ab7cb
-- statement:
--   The theorem states that, for a standard modular datum S on a complex Hilbert space H (a von Neumann algebra M with a unit cyclic and separating vector ξ, a nondegenerate real spectral calculus D with unitary group D.unitary t, an antilinear isometric involution J, and a closed Tomita graph of a ↦ (aξ, a*ξ) over a ∈ M equal to the pairs (p, Jq) where p is mapped to q by the half-exponential graph of D) satisfying ScalarCentralizer (every a in M fixed by conjugation with D.unitary t for all real t is a complex multiple of the identity), the following holds. Let ω be an ultrafilter on ℕ that refines the at-infinity filter (ω ≤ atTop), let T be a bounded complex-linear operator on H, let s be real, and let δₙ > 0 tend to 0. Suppose hₙ are unit vectors, each with spectral support in the interval [s − δₙ, s + δₙ] (every bounded continuous function vanishing on that interval annihilates hₙ under the calculus), and suppose the limsup over n of the ω-limit of the symmetric time averages (1/2k)∫_{−k}^{k} ‖T(D.unitary t hₙ)‖² dt is strictly positive. Then the recovery conclusion holds: there are a strictly increasing sequence nⱼ, operators vⱼ in M, and constants C and η > 0 such that for every j, ‖vⱼ‖ ≤ C, ‖T(vⱼ ξ)‖ ≥ η, and vⱼξ has spectral support in [s − 4δ_{nⱼ}, s + 4δ_{nⱼ}]. The proof is admitted, not supplied.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BoundedRecovery.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BoundedRecovery.lean; bytes 3457..4052
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BoundedRecovery

namespace OAI

universe u

noncomputable section

open Filter MeasureTheory Set

open scoped Topology ComplexConjugate

namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem bounded_recovery (S : StandardModularData H) (hscalar : S.ScalarCentralizer)
    (omega : Ultrafilter ℕ) (hfree : (omega : Filter ℕ) ≤ Filter.atTop)
    (T : H →L[ℂ] H) (s : ℝ) (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n)
    (hdelta0 : Tendsto delta atTop (𝓝 0)) (h : ℕ → H) (hunit : ∀ n, ‖h n‖ = 1)
    (hband : ∀ n, S.D.HasSpectralSupport (Icc (s - delta n) (s + delta n)) (h n))
    (hpositive : 0 < Filter.limsup
      (fun n => fixedMean omega (fun t => ‖T (S.D.unitary t (h n))‖ ^ 2)) atTop) :
    RecoveryConclusion S T s delta := by
  sorry

end BoundedRecovery
end
end OAI
