-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_candidate_approximation
-- name    : LindbladTolerant.Testing.candidate_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:10:13.802559+00:00
-- url     : https://prove2.me/theorems/a4dd2ee9-7458-4960-90c7-cd8dedf2602d
-- title:
--   Lemma 4.1 — Expected approximation error
-- statement:
--   Let $n\ge1$, $d=2^n$, and let $\mathcal L$ be a time-independent $n$-qubit Lindblad generator. All jump representations below use finite traceless jump families and a Hermitian Hamiltonian. Write $C$ for the jump block, $A=\sum_aL_a^\dagger L_a$, $\mathcal D$ for the canonical dissipator, and $\Gamma=\operatorname{Tr}C$. When $\Gamma>0$, put $\sigma=C/\Gamma$, $\sigma_R=\operatorname{Tr}_S\sigma$, and $h(\sigma)=\operatorname{Tr}(\sigma^2)+(d\operatorname{Tr}(\sigma_R^2)-1)/2$.
--
--   Suppose $k\ge1$, the dissipator has locality at most $k$, and $\Gamma>0$. For $m\ge1$ independent Pauli-vector measurements of $\sigma$, let $Q_1,\ldots,Q_m$ be their labels and let $\mathcal C$ consist of the nonidentity strings $P$ of weight at most $k$ whose supports lie in a pairwise union of observed supports. Set $a_P=\operatorname{Tr}(P\sigma_R)$, $G=\sum_{P\ne I}a_P^2$, and $G_{\mathcal C}=\sum_{P\in\mathcal C}a_P^2$. With probability one, every observed label has weight at most $k$ and $|\mathcal C|\le16^k m^2$. Furthermore,
--   $$\mathbb E[G-G_{\mathcal C}]\le\frac{2\cdot16^k(4^k-1)}{em}.$$
--   The expectation is over the first batch. This controls the candidate set's size and its omitted squared coefficients.
--
--   **Formalization Note** Positive-probability finite histories express the almost-sure assertion, and the expectation is its exact finite weighted sum.
--
--   Differences from the source:
--   - encoding: linear operators on the n-qubit Hilbert space → matrices in the fixed bit-string computational basis; reason: the basis representation and normalized matrix-unit formulas preserve every source instance
--   - encoding: almost-sure statements and expectation over independent Pauli labels → all positive-mass finite histories and their Born-weighted finite sum; reason: the measurement alphabet is finite, so these are equivalent and no null history is constrained
--   - encoding: the jump state of a nonzero canonical dissipator → jumpState of a Lindblad generator with a proof that its canonical rate is positive; reason: every canonical dissipator is realized by such a generator; in the traceless Lindblad class nonzero dissipator is equivalent to positive rate, and the proof argument prevents division at zero
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Lemma 4.1, p.19, PDF p.19; Eq.(50)

import Definitions.Def_LindbladTolerant_Testing_estimator

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing

theorem candidate_approximation {n k m : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (g : Super (Qubits n) (Qubits n)) (hl : LocalGenerator k g) (hp : 0 < rate g) :
    (∀ q : Fin m → Pauli n, 0 < discoveryWeight (jumpState g hp) q →
      (∀ j, weight (q j) ≤ k) ∧ (candidateSet k q).card ≤ 16^k * m^2) ∧
    (∑ q : Fin m → Pauli n, discoveryWeight (jumpState g hp) q *
      (marginalG (jumpState g hp) - candidateG (jumpState g hp) (candidateSet k q))) ≤
      2 * (16 : ℝ)^k * ((4 : ℝ)^k - 1) / (Real.exp 1 * (m : ℝ)) := by sorry

end LindbladTolerant.Testing
