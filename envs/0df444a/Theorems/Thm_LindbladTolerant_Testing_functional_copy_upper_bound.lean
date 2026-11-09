-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_functional_copy_upper_bound
-- name    : LindbladTolerant.Testing.functional_copy_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:09:35.383192+00:00
-- url     : https://prove2.me/theorems/5289c432-9fff-457e-9017-441052473c73
-- title:
--   Theorem 4.3 — Copy upper bound
-- statement:
--   Fix $k\ge1$. Choose $C_k$ from the explicit three-batch sizes in the estimator definition, before choosing the number of qubits, the accuracy, or the unknown state. For every $n\ge1$, $0<\delta\le1/16$, and jump state $\sigma$ of a nonzero canonical dissipator of locality at most $k$, the fixed discovery, product-Pauli, and full-SR SWAP routine outputs a bounded estimate and obeys
--   $$0\le\widehat h\le\frac{2^k+1}{2},\qquad
--   \Pr\{|\widehat h-h(\sigma)|\le\delta\}\ge\frac{99}{100}.$$
--   Its copy count satisfies
--   $$S(k,\delta)=m+N+2s\le\lceil C_k\delta^{-2}\rceil,\qquad C_k\ge1.$$
--   Here $h(\sigma)=\operatorname{Tr}(\sigma^2)+(2^n\operatorname{Tr}(\sigma_R^2)-1)/2$ and $\sigma_R$ is the reference marginal. All batches and constants depend only on $k,\delta$, so one algorithm works for all promised states in a fixed dimension.
--
--   This is the dimension-independent copy upper bound used in Algorithm 1.
--
--   **Formalization Note** With $\beta=1/300$, $K_k=2\cdot16^k(4^k-1)/e$, $a_k=2K_k/\beta$, $b_k=32\cdot6^k(2^k-1)/\beta$, and $d_k=8\cdot6^k4^k/\sqrt\beta$, the explicit coefficient is $C_k=\lceil a_k+4+\max(b_k,d_k(a_k+1))+16\log(2/\beta)\rceil$. This follows from the displayed batch sizes and $\lceil x\rceil\le x+1$, without changing the paper's $O_k(\delta^{-2})$ claim.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
--   - encoding: existence of an algorithm using O_k(delta^-2) copies → the explicit algorithm in the proof and the displayed ceiling-derived C_k bound; reason: the proof gives this fixed routine uniformly in n and its state, and ceiling bounds make the implicit constant explicit
--   - encoding: the jump state of a nonzero canonical dissipator → jumpState of a Lindblad generator with a proof that its canonical rate is positive; reason: every canonical dissipator is realized by such a generator; in the traceless Lindblad class nonzero dissipator is equivalent to positive rate, and the proof argument prevents division at zero
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Theorem 4.3, p.22, PDF p.22; proof and exact batch sizes pp.22–23, PDF pp.22–23

import Definitions.Def_LindbladTolerant_Testing_estimator

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem functional_copy_upper_bound :
    ∀ k : ℕ, 1 ≤ k → 1 ≤ copyConstant k ∧
    ∀ n : ℕ, 1 ≤ n → ∀ delta : ℝ, 0 < delta → delta ≤ 1/16 →
      copyCount k delta ≤ ⌈copyConstant k * delta⁻¹^2⌉₊ ∧
      (∀ x : EstimatorSample n k delta,
        0 ≤ estimatorValue k delta x ∧ estimatorValue k delta x ≤ functionalBound k) ∧
      ∀ g : Super (Qubits n) (Qubits n), LocalGenerator k g → ∀ hp : 0 < rate g,
        99/100 ≤ estimatorProbability (jumpState g hp) k delta
          (fun h => |h - functional (jumpState g hp)| ≤ delta) := by sorry

end LindbladTolerant.Testing
