-- Prove2me | Theorems.Thm_OAI_QAC_parity_lower_bound_polynomial_size
-- name    : OAI.QAC.parity_lower_bound_polynomial_size
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:12.743991+00:00
-- url     : https://prove2.me/theorems/6faa7fa7-d334-44cf-8819-ee227f1a876b
-- statement:
--   The theorem states that, for any positive integers d, k and C, there is a threshold n₀ such that for every n ≥ n₀ and every total qubit count N with n ≤ N ≤ C(n+1)^k, the following holds. Take any circuit given as a list of at most d physical layers on N qubits, where a layer is a list of gates with pairwise disjoint supports and each gate is either a one-qubit unitary on a single qubit or a Toffoli gate with an arbitrary finite set of control qubits and a target outside that set (flipping the target exactly when all controls are 1). The circuit's matrix is the product of the layer matrices, with the first layer acting first. For every choice of output qubit out among the N qubits, there exists an n-bit input x such that successProbability, the total Born probability over all final computational-basis strings y whose out-th bit equals the parity (sum mod 2) of x, is strictly less than 2/3. Here the input state is x placed on the first n qubits with all remaining qubits set to 0, and the remaining qubits are summed over with no requirement that they be clean. So fixed-depth circuits with polynomially many qubits cannot compute parity with worst-case success probability at least 2/3. The theorem is admitted in the source (proof is sorry).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RegularParity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RegularParity.lean; bytes 2163..2689
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_RegularParity

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

/-- Fixed-depth circuits with polynomially many total qubits cannot compute parity
with worst-case success at least two thirds. -/
theorem parity_lower_bound_polynomial_size (d k C : ℕ)
    (_hd : 0 < d) (_hk : 0 < k) (_hC : 0 < C) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, n ≤ N → N ≤ C * (n + 1) ^ k →
      ∀ layers : List (PhysicalLayer N), layers.length ≤ d →
        ∀ out : Fin N, ∃ x : Word n,
          successProbability (physicalCircuitMatrix layers) out x < (2 : ℝ) / 3 := by
  sorry

end QAC
end
end OAI
