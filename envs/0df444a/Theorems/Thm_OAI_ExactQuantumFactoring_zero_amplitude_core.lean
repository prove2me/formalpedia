-- Prove2me | Theorems.Thm_OAI_ExactQuantumFactoring_zero_amplitude_core
-- name    : OAI.ExactQuantumFactoring.zero_amplitude_core
-- status  : Open
-- author  : @SamenHossain
-- created : 2026-10-12T05:28:09.813061+00:00
-- url     : https://prove2.me/theorems/24158f22-8cd9-4229-8dee-ddf1cbc66bf5
-- title:
--   Exact quantum factoring core: a uniform polynomial circuit family with zero amplitude on wrong outputs
-- statement:
--   There is a circuit family $(C_\ell)_\ell$ over the fixed gate set with the following properties:
--   - it is generated uniformly from the unary input length by a polynomial-time Turing machine with finite stack alphabets;
--   - it has polynomially many qubits and instructions;
--   - for every $N\ge2$ of bit length $\ell$, the circuit has at least $\ell+n^2$ qubits with $n=\max(128,\ell)$;
--   - the output state on input $N$ has amplitude $0$ on every basis state whose $n$ output blocks do not encode the complete nondecreasing prime factorization of $N$, padded with zeros.
--
--   Together with conservation of total probability, which is the proved sibling `outputState_normSq_sum`, this is equivalent to the mission goal that the circuits output the factorization with probability exactly $1$.
--
--   **Formalization Note** Circuits, gates, the output state, the output decoding `outputList` and `CorrectEncoding` are those of the published definition `ExactQuantumFactoring`. A basis state is a function from wires to Booleans, and the output state is a complex vector indexed by basis states.
-- source:
--   OpenAI, "Exact quantum factoring over a fixed finite gate set" (September 25, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; goal theorem OAI.ExactQuantumFactoring.exact_quantum_factoring of the mission "Exact quantum factoring over a fixed finite gate set"

import Mathlib
import Definitions.Def_ExactQuantumFactoring

namespace OAI

namespace ExactQuantumFactoring

open scoped BigOperators

/-- **Exact factoring core: no amplitude on wrong outputs.** A uniform, polynomial-size circuit
family over the fixed gate set whose output state on every input `N ≥ 2` of bit length `ℓ` has zero
amplitude on every basis state that does not encode the complete sorted prime factorization of `N`. -/
theorem zero_amplitude_core :
    ∃ family : ℕ → Circuit, Uniform family ∧ PolynomialResources family ∧
      ∀ (ℓ N : ℕ), 2 ≤ N → N.size = ℓ →
        ℓ + (paddedLength ℓ)^2 ≤ (family ℓ).qubits ∧
        ∀ x : Basis (family ℓ).qubits,
          ¬ CorrectEncoding N (paddedLength ℓ) (outputList ℓ x) →
            (family ℓ).outputState ℓ N x = 0 := by
  sorry

end ExactQuantumFactoring
end OAI
