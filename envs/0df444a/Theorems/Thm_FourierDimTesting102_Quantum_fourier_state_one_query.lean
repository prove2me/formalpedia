-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_fourier_state_one_query
-- name    : FourierDimTesting102.Quantum.fourier_state_one_query
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:07:16.894196+00:00
-- url     : https://prove2.me/theorems/9ad15198-408c-467e-9edf-ef90d45075b0
-- title:
--   Lemma 3.1: one quantum query prepares the Fourier-amplitude state
-- statement:
--   Let $f:\mathbb F_2^n\to\{-1,1\}$ be a boolean function. The fixed algorithm that starts in $|0^n\rangle|1\rangle$, applies Hadamard gates to all qubits, makes one query to the XOR oracle $O_f$ and applies Hadamard gates again ends in the state
--
--   $$
--   |\psi_f\rangle\otimes|1\rangle,\qquad |\psi_f\rangle=\sum_{s\in\mathbb F_2^n}\widehat f(s)\,|s\rangle.
--   $$
--
--   The amplitudes are the signed real Fourier coefficients. Measuring the state therefore samples $s$ with probability $\widehat f(s)^2$. This is the sampling primitive that the tester of Theorem 3.1 amplifies.
--
--   **Formalization Note** The algorithm `prepAlg n` is defined without reference to $f$, so one algorithm serves all $f$, and its type records that it makes exactly one query.
--
--   Differences from the source:
--   - encoding: boolean functions f : {0,1}^n → {−1,1}, with frequencies written as subsets S ⊆ [n] or their indicator vectors → f is its bit function BoolFn n := (Fin n → ZMod 2) → Bool, with sign toSign f x = (−1)^{f x}, and frequencies are vectors of Fin n → ZMod 2; reason: a bijection on the same functions; the bit is what the XOR oracle adds and the vectors carry the F₂-subspaces
--   - encoding: there is an algorithm which uses 1 quantum query and produces the state |ψ⟩ → the named algorithm prepAlg n, with register (V n × Bool) × Fin 1, ends in |ψ_f⟩ ⊗ |1⟩ ⊗ |0⟩; reason: the XOR oracle needs a target bit, which ends in a fixed state independent of f; naming the algorithm before f gives the frozen algorithm the query model requires
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.13, Lemma 3.1

import Definitions.Def_FourierDimTesting102_Quantum_Algorithm

namespace FourierDimTesting102.Quantum

open QAlgorithms

/-- Lemma 3.1, p.13: the frozen one-query algorithm `prepAlg n` leaves, for every boolean `f`, the
state `|ψ_f⟩ = ∑_s f̂(s)|s⟩` in the input register, with the target bit back in the fixed state
`|1⟩` and the one-point workspace unchanged. -/
theorem fourier_state_one_query (n : ℕ) (f : BoolFn n) :
    (prepAlg n).finalState (xorOracle f) =
      tensorVec (tensorVec (fourierState f) (ket true)) (ket (0 : Fin 1)) := by sorry

end FourierDimTesting102.Quantum
