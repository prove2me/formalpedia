-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_conditional_variance
-- name    : LindbladTolerant.Testing.conditional_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:09:26.132275+00:00
-- url     : https://prove2.me/theorems/31523f87-9bac-4022-9fb2-91f6315b3082
-- title:
--   Lemma 4.2 — Conditional variance
-- statement:
--   Let $n\ge1$, $d=2^n$, and let $\mathcal L$ be a time-independent $n$-qubit Lindblad generator. All jump representations below use finite traceless jump families and a Hermitian Hamiltonian. Write $C$ for the jump block, $A=\sum_aL_a^\dagger L_a$, $\mathcal D$ for the canonical dissipator, and $\Gamma=\operatorname{Tr}C$. When $\Gamma>0$, put $\sigma=C/\Gamma$, $\sigma_R=\operatorname{Tr}_S\sigma$, and $h(\sigma)=\operatorname{Tr}(\sigma^2)+(d\operatorname{Tr}(\sigma_R^2)-1)/2$.
--
--   Suppose $k\ge1$ and the nonzero dissipator has locality at most $k$. Condition on $m\ge1$ independent discovery labels $Q_1,\ldots,Q_m$, forming the candidate set $\mathcal C$. Use $N\ge2$ fresh independent copies for product-Pauli record vectors, and let $\widehat G$ be the sum of their ordered distinct-pair inner products divided by $N(N-1)$. With $G_{\mathcal C}=\sum_{P\in\mathcal C}(\operatorname{Tr}(P\sigma_R))^2$,
--   $$\mathbb E[\widehat G\mid Q_1,\ldots,Q_m]=G_{\mathcal C},$$
--   $$\operatorname{Var}(\widehat G\mid Q_1,\ldots,Q_m)\le\frac{4\cdot6^k(2^k-1)}N+\frac{4\cdot16^k6^{2k}m^2}{N^2}.$$
--   Both conclusions hold at every positive-probability first-batch history, equivalently almost surely. These are the conditional unbiasedness and fluctuation guarantees needed by the functional estimator. Entries in a single record may be correlated; fresh copies, rather than record entries, are independent.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
--   - encoding: conditional mean and variance given the first batch → finite fresh-record Born sums at each positive-mass first-batch history; reason: finite conditioning is equivalent to the almost-sure conditional identities and requires no hypothesis about null histories
--   - encoding: the jump state of a nonzero canonical dissipator → jumpState of a Lindblad generator with a proof that its canonical rate is positive; reason: every canonical dissipator is realized by such a generator; in the traceless Lindblad class nonzero dissipator is equivalent to positive rate, and the proof argument prevents division at zero
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Lemma 4.2, p.21, PDF p.21; Eqs.(68)–(69)

import Definitions.Def_LindbladTolerant_Testing_estimator

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem conditional_variance {n k m N : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m) (hN : 2 ≤ N)
    (g : Super (Qubits n) (Qubits n)) (hl : LocalGenerator k g) (hp : 0 < rate g) :
    ∀ q : Fin m → Pauli n, 0 < discoveryWeight (jumpState g hp) q →
      conditionalMean (jumpState g hp) k q N = candidateG (jumpState g hp) (candidateSet k q) ∧
      conditionalVariance (jumpState g hp) k q N ≤
        4 * (6 : ℝ)^k * ((2 : ℝ)^k - 1) / (N : ℝ) +
        4 * (16 : ℝ)^k * (6 : ℝ)^(2*k) * (m : ℝ)^2 / (N : ℝ)^2 := by sorry

end LindbladTolerant.Testing
