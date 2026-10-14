-- Prove2me | Theorems.Thm_OAI_ExactQuantumFactoring_outputState_normSq_sum
-- name    : OAI.ExactQuantumFactoring.outputState_normSq_sum
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-12T05:27:40.888248+00:00
-- url     : https://prove2.me/theorems/8ae605c8-4388-476b-a44c-88110962f7bd
-- title:
--   Circuits over the fixed gate set preserve total probability
-- statement:
--   Let $c$ be any circuit over the fixed alphabet of $20$ gates: NOT, CNOT, Toffoli, Hadamard and the phase gate $\mathrm{diag}(1,i)$, each optionally inverted and optionally given one extra control. Then for every input length $\ell$ and integer $N$, the output state $\psi=c(|N\rangle)$ satisfies
--   $$\sum_{x}|\psi(x)|^2=1 .$$
--
--   Each gate matrix is unitary on its wires, and acting on distinct wires while fixing all other wires gives a unitary on the full space. Products of unitaries preserve the $\ell^2$ norm, and the initial basis vector has norm $1$. Consequently, success probability exactly $1$ is equivalent to zero amplitude on every incorrect output.
--
--   **Formalization Note** Circuits, gates, the output state, the output decoding `outputList` and `CorrectEncoding` are those of the published definition `ExactQuantumFactoring`. A basis state is a function from wires to Booleans, and the output state is a complex vector indexed by basis states.
-- source:
--   OpenAI, "Exact quantum factoring over a fixed finite gate set" (September 25, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; goal theorem OAI.ExactQuantumFactoring.exact_quantum_factoring of the mission "Exact quantum factoring over a fixed finite gate set"; Section 2 (gate set and circuit semantics)

import Mathlib
import Definitions.Def_ExactQuantumFactoring

namespace OAI

namespace ExactQuantumFactoring

open scoped BigOperators

/-- **Circuits preserve total probability.** Every circuit over the fixed 20-gate alphabet acts
unitarily, so the output state on any classical input has total squared amplitude `1`. -/
theorem outputState_normSq_sum (c : Circuit) (ℓ N : ℕ) :
    ∑ x : Basis c.qubits, Complex.normSq (c.outputState ℓ N x) = 1 := by
  sorry

end ExactQuantumFactoring
end OAI
