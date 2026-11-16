-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_Supplement_functional_copy_lower_bound
-- name    : LindbladTolerant.Testing.Supplement.functional_copy_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:13:37.973987+00:00
-- url     : https://prove2.me/theorems/2095b958-ae08-404c-a291-3dc58c527531
-- title:
--   Theorem 4.5 — Copy lower bound: estimating $h(\sigma)$ to accuracy $\delta$ needs $N\ge 1/(144\delta^2)$ copies
-- statement:
--   Fix a locality bound $k\ge1$, a number of qubits $n\ge1$ and an accuracy $0<\delta\le 1/16$. Let $\sigma$ range over the jump states $\sigma=C/\Gamma$ of $n$-qubit Lindblad generators whose canonical dissipator is nonzero ($\Gamma=\operatorname{Tr}C>0$) and admits a representation by traceless jump operators each supported on at most $k$ qubits. Write
--   $$
--   h(\sigma)=\operatorname{Tr}(\sigma^2)+\tfrac12\bigl(d\operatorname{Tr}(\sigma_R^2)-1\bigr),\qquad d=2^n,\ \sigma_R=\operatorname{Tr}_S\sigma .
--   $$
--
--   Let $N\ge0$ be an integer and let $\mathcal M$ be any quantum instrument acting on $N$ independent copies $\sigma^{\otimes N}$, with real outcome $\hat h$ (and an arbitrary finite quantum output), chosen without knowledge of $\sigma$. If, for every such $\sigma$,
--   $$
--   \Pr\bigl[\,|\hat h-h(\sigma)|\le\delta\,\bigr]\ \ge\ \tfrac23 ,
--   $$
--   then
--   $$
--   N\ \ge\ \frac{1}{144\,\delta^{2}} .
--   $$
--
--   Since the instrument acts jointly on all $N$ copies and may include ancillas and internal randomness, the bound holds for arbitrary adaptive and collective measurements. It matches the $O_k(\delta^{-2})$ copy upper bound of Theorem 4.3, so the $\delta$-dependence of that estimator is optimal for fixed $k$. This is a companion result: the time-testing goal (Theorem 1.1) does not use it.
--
--   **Formalization Note** The paper's $\Omega(\delta^{-2})$ is made explicit with the constant $1/144$ that its proof derives (p. 25, after Eq. (93)); this constant is uniform in $k$, $n$ and $\delta$. $N=0$ is allowed (no copies; the input is the scalar $1$), and then the conclusion says that no such estimator exists. The class of $\sigma$ is the same one used for the published Theorem 4.3.
--
--   Differences from the source:
--   - encoding: $\Omega(\delta^{-2})$ copies → $N\ge 1/(144\delta^2)$; reason: the explicit constant 1/144 is the one derived in the source's proof (p. 25, Eqs. (90), (93)); it is uniform in $k$, $n$, $\delta$, so the asymptotic claim is implied
--   - encoding: any estimator accessing $\sigma$ only through independent copies, with arbitrary adaptive and collective measurements → any quantum instrument (arbitrary Borel real outcome, CP branches, Born law) acting on $\sigma^{\otimes N}$, where $N$ is the worst-case number of copies; reason: the source's proof (p. 25) supplies all $N$ copies at the start and views the whole procedure, including internal randomness, as one measurement on $\sigma^{\otimes N}$; every adaptive procedure with ancillas has such a joint instrument
--   - encoding: jump states of nonzero canonical dissipators with locality at most $k$ → jump states of Lindblad generators with a $k$-local traceless representation and positive canonical rate; reason: the canonical dissipator is nonzero exactly when its jump rate is positive, and this is the class of the published Theorem 4.3
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, STOC 2027 submission #238 (October 2026), Optimal Tolerant Testing of Lindbladian Dissipation, SHA-256 d5f3c8d172d2da31a25deb28abf000f92655ed8e1a5a4c07bbd67d8676f759e8; p.24 (PDF p.24), Theorem 4.5; proof pp.24–25 (PDF pp.24–25), constant 1/144 after Eq. (93); task Eq. (46), p.18.

import Definitions.Def_LindbladTolerant_Testing_Supplement_copy_estimation

set_option autoImplicit false
open scoped ComplexOrder

namespace LindbladTolerant.Testing.Supplement

open LindbladTolerant.Testing

theorem functional_copy_lower_bound (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta' : delta ≤ 1/16) (N : ℕ)
    {O : ℝ → Type} [∀ o, Fintype (O o)] [∀ o, DecidableEq (O o)]
    (a : QuantumInstrument (Fin N → Qubits n × Qubits n) O)
    (ha : CopyEstimates k delta a) :
    1 / (144 * delta^2) ≤ (N : ℝ) := by sorry

end LindbladTolerant.Testing.Supplement
