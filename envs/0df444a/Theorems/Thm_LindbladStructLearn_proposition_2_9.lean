-- Prove2me | Theorems.Thm_LindbladStructLearn_proposition_2_9
-- name    : LindbladStructLearn.proposition_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:59:58.306198+00:00
-- url     : https://prove2.me/theorems/d7bbc7e4-73c8-44b9-8756-05153f1a459b
-- title:
--   Proposition 2.9 — single-sample estimates of Algorithm 1 are unbiased
-- statement:
--   Let $\Phi$ be a superoperator on $n$ qubits and $\overline P = (P_1, P_2)$ a pair of Paulis. In one sample of Algorithm 1, $A$ and $B$ are uniform on $\mathcal P_n$, $v$ is uniform on $\{\pm1\}^n$, the state $|A,v\rangle$ is prepared, $\Phi$ is applied, and the outcome $w$ of the measurement in the eigenbasis of $B$ has probability $\mathrm{tr}(|B,w\rangle\langle B,w|\cdot\Phi(|A,v\rangle\langle A,v|))$. The single-sample estimate $E_{P_1,P_2}$ of (2.27)–(2.28) then satisfies
--
--   $$\sum_{A,v,B,w} \frac{1}{4^n\,2^n\,4^n}\,\mathrm{tr}\big(|B,w\rangle\langle B,w|\cdot\Phi(|A,v\rangle\langle A,v|)\big)\, E_{P_1,P_2}(A,v,B,w) = \widehat\Phi_{\mathrm{loc}}(P_1,P_2),$$
--
--   i.e. it is an unbiased estimator of the local Fourier coefficient.
--
--   This is the statistical core of Algorithm 1: one random Pauli-eigenstate experiment yields an unbiased estimate of every local Fourier coefficient at once.
--
--   Differences from the source:
--   - generalization: Φ an n-qubit quantum channel (the input of Algorithm 1) → Φ any superoperator, with the Born expression as the weight; reason: the identity is linear in Φ and the paper's proof uses only linearity; channels are a special case
--   - generalization: P1, P2 with s_P̄ ≤ k, for the locality parameter k of Algorithm 1 → every pair P̄; reason: k is arbitrary in Algorithm 1, so every pair is covered by some k; the estimator does not depend on k
--   - encoding: E^(i) is an unbiased estimator (an expectation over one sample) → the explicit finite sum over (A, v, B, w) with weights 4^{-n}·2^{-n}·4^{-n}·Born probability; reason: the sampling law of one iteration of Algorithm 1 written out
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Proposition 2.9, p.16; Algorithm 1, p.17

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_alg1Sample
import Definitions.Def_LindbladStructLearn_bornAmp
import Definitions.Def_LindbladStructLearn_locFourier

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Proposition 2.9 (single sample unbiased estimators; Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.16, with Algorithm 1,
p.17): the single-sample quantity `E^(i)_(P₁,P₂)` of Algorithm 1 is an unbiased estimator of
`Φ̂_loc(P₁,P₂)`. In one sample, `A` and `B` are uniform on `𝒫_n`, `v` is uniform on `{±1}ⁿ`, and
the outcome `w` has probability `tr(|B,w⟩⟨B,w| · Φ(|A,v⟩⟨A,v|))` (Eq. (2.30)).

**Formalization Note** The expectation is the explicit finite sum over `(A, v, B, w)`. It is stated
for every superoperator `Φ` (linear algebra; for a quantum channel the weights are the outcome
probabilities) and for every pair `P̄` (the paper's `s_P̄ ≤ k` with `k` arbitrary). -/
theorem proposition_2_9 {n : ℕ} (Φ : Super (Qubits n) (Qubits n)) (P : Pauli n × Pauli n) :
    ∑ A : Pauli n, ∑ v : Qubits n, ∑ B : Pauli n, ∑ w : Qubits n,
      ((1 / 4 ^ n : ℂ) * (1 / 2 ^ n) * (1 / 4 ^ n)) * bornAmp Φ A v B w * alg1Sample P A v B w =
      locFourier Φ P := by sorry

end LindbladStructLearn
