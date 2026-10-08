-- Prove2me | Theorems.Thm_OAI_QAC_parity_lower_bound
-- name    : OAI.QAC.parity_lower_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:12.470994+00:00
-- url     : https://prove2.me/theorems/40a0f85d-beb7-492a-8b59-12a13d9eac47
-- statement:
--   The theorem states that the defined proposition QAC.ParityStatement holds, a measured-output lower bound for computing parity with constant-depth circuits of one-qubit unitaries and unbounded-arity Toffoli gates on polynomially many qubits. Here a physical layer is a list of gates with pairwise disjoint supports (a one-qubit unitary acts on its qubit; a Toffoli with a control set and a target outside it flips the target exactly when all controls are 1), a circuit is a list of layers whose matrices are multiplied with the first layer acting first, and the input is x in {0,1}^n padded with zeros to N qubits. The success probability for a designated output qubit is the total Born probability of all final basis states whose output bit equals the parity of x, summed over all garbage on the other qubits with no cleanliness assumption. The statement is: for every depth bound d, every c ≥ 1 and every 0 < ε ≤ 1/2, there is n₀ such that for all n ≥ n₀, all N with n ≤ N ≤ n^c, all circuits with at most d layers on N qubits, and every output qubit, it is not the case that the success probability is at least 1/2 + ε for every input x in {0,1}^n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/QACParity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/QACParity.lean; bytes 2639..2705
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_QACParity

namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

theorem QAC.parity_lower_bound : QAC.ParityStatement := by
  sorry

end
end OAI
