-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_Supplement_lemma_5_8
-- name    : NoMenuRevenue186.TrustedXOS.Supplement.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:07:36.206286+00:00
-- url     : https://prove2.me/theorems/ef9889fc-3b31-4def-978e-72d0609e0637
-- title:
--   Lemma 5.8 — hypercontractive bound for a noisy pair
-- statement:
--   Let $X$ be uniform on $\{0,1\}^m$ and let $Y$ be obtained from $X$ by flipping each coordinate independently with probability $(1-\rho)/2$, where $0\le\rho\le1$. Let $\nu$ be the uniform measure on $\mathcal V=\{0,1\}^m\times[K]$ and $\mathcal V_j=\{0,1\}^m\times\{j\}$. For all colors $j,k\in[K]$ and all $P\subseteq\mathcal V_j$, $Q\subseteq\mathcal V_k$,
--
--   $$\Pr\bigl[(X,j)\in P,\ (Y,k)\in Q\bigr]\le\bigl(K^2\,\nu(P)\,\nu(Q)\bigr)^{1/(1+\rho)}.$$
--
--   This is a form of Boolean hypercontractivity (Bonami–Beckner); it bounds the probability that two correlated petal sets reach the same small stopping node of the protocol.
--
--   Differences from the source:
--   - encoding: the probability of the event under the noisy pair (X, Y) → an explicit finite sum over x in the fiber of P and y in the fiber of Q of 2^{-m} ((1-rho)/2)^{dist} ((1+rho)/2)^{m-dist}; reason: the exact law of independent coordinate flips; colors are natural numbers restricted to [K] = {1..K}
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.29, PDF p.31, Lemma 5.8; proof Appendix B.2, printed p.39, PDF p.41

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Supplement_Strings

namespace NoMenuRevenue186.TrustedXOS.Supplement
open NoMenuRevenue186.TrustedXOS

/-- Lemma 5.8, printed p.29 (PDF p.31), proof in Appendix B.2. `X` uniform on `{0,1}^m`,
    `Y` from `X` by independent flips with probability `(1 - ρ)/2`, `0 ≤ ρ ≤ 1`. For colors
    `j, k ∈ [K]` and `P ⊆ V_j`, `Q ⊆ V_k`:
    `Pr[(X,j) ∈ P, (Y,k) ∈ Q] ≤ (K² ν(P) ν(Q))^{1/(1+ρ)}`. -/
theorem lemma_5_8 (m K : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (j k : ℕ) (hj : j ∈ Finset.Icc 1 K) (hk : k ∈ Finset.Icc 1 K)
    (P Q : Finset (BitString m × ℕ)) (hP : P ⊆ slice m j) (hQ : Q ⊆ slice m k) :
    noisyPairProb m ρ (fiber P j) (fiber Q k) ≤
      ((K : ℝ) ^ 2 * refMeasure m K P * refMeasure m K Q) ^ (1 / (1 + ρ)) := by sorry

end NoMenuRevenue186.TrustedXOS.Supplement
