-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_Supplement_lemma_5_9
-- name    : NoMenuRevenue186.TrustedXOS.Supplement.lemma_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:08:06.815565+00:00
-- url     : https://prove2.me/theorems/8326ec5b-cba6-47d9-b521-92a774f23840
-- title:
--   Lemma 5.9 — the same bound for exact-weight perturbations
-- statement:
--   Let $m\ge1$ and $0\le d\le m$. Let $C$ be uniform on $\{0,1\}^m$ and let $E,E'$ be independent and uniform over the strings of Hamming weight exactly $d$, independent of $C$. Put
--
--   $$X=C\oplus E,\qquad Y=C\oplus E',\qquad \rho=\Bigl(1-\frac{2d}{m}\Bigr)^2.$$
--
--   Then for all colors $j,k\in[K]$ and all $P\subseteq\mathcal V_j$, $Q\subseteq\mathcal V_k$ (with $\nu$ the uniform measure on $\mathcal V=\{0,1\}^m\times[K]$),
--
--   $$\Pr\bigl[(X,j)\in P,\ (Y,k)\in Q\bigr]\le(m+1)^2\bigl(K^2\,\nu(P)\,\nu(Q)\bigr)^{1/(1+\rho)}.\qquad(5.2)$$
--
--   This transfers Lemma 5.8 to the exact petal-generating process of the hard instance, where two petals of one neighborhood are independent weight-$d$ perturbations of a common center.
--
--   Differences from the source:
--   - generalization: d = floor(2m/K) as in Section 5.1 → any natural d with d <= m, and m >= 1; reason: the statement of Lemma 5.9 and its proof use only that weight-d strings exist and that d/m is defined; the source parameter is an instance
--   - encoding: the probability of the event under (C xor E, C xor E') → the explicit finite average over c and over pairs of weight-d strings; reason: the exact law of the uniform independent choices; colors are natural numbers restricted to [K] = {1..K}
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.30, PDF p.32, Lemma 5.9, eq. (5.2); proof Appendix B.2, printed p.40, PDF p.42

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Supplement_Strings

namespace NoMenuRevenue186.TrustedXOS.Supplement
open NoMenuRevenue186.TrustedXOS

/-- Lemma 5.9, printed p.30 (PDF p.32), proof in Appendix B.2. `C` uniform on `{0,1}^m`,
    `E, E'` independent uniform strings of weight exactly `d`, `X = C ⊕ E`, `Y = C ⊕ E'`,
    `ρ = (1 - 2d/m)²`. For colors `j, k ∈ [K]` and `P ⊆ V_j`, `Q ⊆ V_k`:
    `Pr[(X,j) ∈ P, (Y,k) ∈ Q] ≤ (m + 1)² (K² ν(P) ν(Q))^{1/(1+ρ)}`, eq. (5.2). -/
theorem lemma_5_9 (m K d : ℕ) (hm : 1 ≤ m) (hd : d ≤ m)
    (j k : ℕ) (hj : j ∈ Finset.Icc 1 K) (hk : k ∈ Finset.Icc 1 K)
    (P Q : Finset (BitString m × ℕ)) (hP : P ⊆ slice m j) (hQ : Q ⊆ slice m k) :
    weightPairProb m d (fiber P j) (fiber Q k) ≤
      ((m : ℝ) + 1) ^ 2 *
        ((K : ℝ) ^ 2 * refMeasure m K P * refMeasure m K Q) ^
          (1 / (1 + (1 - 2 * (d : ℝ) / (m : ℝ)) ^ 2)) := by sorry

end NoMenuRevenue186.TrustedXOS.Supplement
