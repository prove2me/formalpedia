-- Prove2me | Theorems.Thm_OAI_EntropyPhotonNumber_entropy_photon_number_inequality
-- name    : OAI.EntropyPhotonNumber.entropy_photon_number_inequality
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:37.05952+00:00
-- url     : https://prove2.me/theorems/e96b6eda-42d9-4886-afaa-616a4ea529c2
-- statement:
--   The theorem states that, for any positive number n of bosonic modes, with states being positive bounded operators on the full Fock space ℓ²(ℕⁿ,ℂ) whose number-basis diagonal real parts sum to 1, and for states ρA, ρB, ρC where ρA and ρB have finite energy, meaning summable total-number-weighted diagonal entries (the expected total photon number is finite), and any transmissivity η in [0,1], the following holds whenever ρC is the beam-splitter output of ρA and ρB at η. Here the output condition means that every number-basis matrix entry of ρC is the sum of the series defining the discarded-port block of the passive two-port mixing of ρA⊗ρB, with the same rotation (√η, −√(1−η); √(1−η), √η) applied in every mode, so internal entanglement within each input is allowed. Writing S for the von Neumann entropy −Tr ρ log ρ, g(t) = (t+1)log(t+1) − t log t for the thermal entropy per mode, and gInv(s) for the infimum of those t ≥ 0 with g(t) ≥ s, the conclusion is η·gInv(S(ρA)/n) + (1−η)·gInv(S(ρB)/n) ≤ gInv(S(ρC)/n). Finite energy is assumed only for the two inputs, and the theorem is stated as admitted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EntropyPhotonNumber.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EntropyPhotonNumber.lean; bytes 4307..4778
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_EntropyPhotonNumber

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber

/-- The entropy photon-number inequality for arbitrary finite-energy inputs
and any positive finite number of modes. -/
theorem entropy_photon_number_inequality
    (n : ℕ) (hn : 1 ≤ n) (ρA ρB ρC : State n)
    (hA : FiniteEnergy ρA) (hB : FiniteEnergy ρB)
    (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hC : IsBeamSplitterOutput η ρA ρB ρC) :
    η * gInv (entropy ρA / n) + (1 - η) * gInv (entropy ρB / n) ≤
      gInv (entropy ρC / n) := by
  sorry

end EntropyPhotonNumber
end
end OAI
