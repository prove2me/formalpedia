-- Prove2me | Theorems.Thm_GaussMixHH_lemma_17
-- name    : GaussMixHH.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:33.972194+00:00
-- url     : https://prove2.me/theorems/c9c7e9a3-8e29-4a5c-ac12-e2b50903d967
-- title:
--   Lemma 17, p.24 — majority amplification: an odd $k=\Theta(\log(1/\eta))$ with $P_k$ $\eta/4$-close to a threshold and $\sum|a_j|\le3^k$
-- statement:
--   There are universal constants $c,C>0$ such that for every $0<\eta<1/4$ there is an odd integer $k$ with $c\log(1/\eta)\le k\le C\log(1/\eta)$ for which, writing $h=(k+1)/2$ and
--
--   $$P_k(x)=\Pr_{B\sim\mathrm{Bin}(k,x)}[B\ge h]=\sum_{\ell=h}^{k}\binom k\ell x^\ell(1-x)^{k-\ell}=\sum_{j=h}^{k}a_jx^j,$$
--
--   1. every monomial of $P_k$ has degree between $h$ and $k$ ($a_j=0$ for $j<h$ and $j>k$);
--   2. $0\le P_k(x)\le1$ on $[0,1]$;
--   3. $|P_k(x)-1|\le\eta/4$ for $e^{-1/4}\le x\le1$, and $|P_k(x)|\le\eta/4$ for $0\le x\le e^{-1}$;
--   4. $\sum_{j=h}^{k}|a_j|\le3^k$.
--
--   With $x=e^{-r^2/R^2}$ this gives a short combination of exponential tests that separates radii $\le R/2$ from radii $\ge R$, with controlled coefficients.
--
--   Differences from the source:
--   - encoding: k = Θ(log(1/η)) → c·log(1/η) ≤ k ≤ C·log(1/η) with universal c, C chosen before η; reason: the meaning of Θ
--   - encoding: "every monomial of P_k has degree between h and k" → (majorityPoly k).coeff j = 0 for j < h and for j > k; reason: the parenthetical claim as a conclusion
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 17, p.24 (PDF p.26); η ∈ (0, 1/4) fixed at the start of §4.3, p.23

import Mathlib
import Definitions.Def_GaussMixHH_MajorityPoly

open Polynomial

namespace GaussMixHH

/-- **Lemma 17** (Majority amplification).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Lemma 17, p.24 (PDF p.26), with
`0 < η < 1/4` fixed at the start of §4.3, p.23.

"There is an odd integer k = Θ(log(1/η)) for which the following holds. Write h = (k + 1)/2 and
define P_k(x) := Pr_{B∼Bin(k,x)}[B ≥ h] = Σ_{ℓ=h}^{k} (k choose ℓ) x^ℓ(1 − x)^{k−ℓ} = Σ_{j=h}^{k} a_j x^j
(note that every monomial of P_k has degree between h = (k + 1)/2 and k). Then 0 ≤ P_k(x) ≤ 1 on
[0, 1], and |P_k(x) − 1| ≤ η/4 (e^{−1/4} ≤ x ≤ 1), |P_k(x)| ≤ η/4 (0 ≤ x ≤ e^{−1}),
Σ_{j=h}^{k} |a_j| ≤ 3^k."

**Formalization Note.** `k = Θ(log(1/η))` is `c·log(1/η) ≤ k ≤ C·log(1/η)` with universal `c, C`
chosen before `η`. `a_j` is `(majorityPoly k).coeff j`; the parenthetical degree claim is the
conclusion that `a_j = 0` for `j < h` and for `j > k`. The two approximation bounds are
`MajorityApprox k η`. -/
theorem lemma_17 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ η : ℝ, 0 < η → η < 1 / 4 →
        ∃ k : ℕ, Odd k ∧ c * Real.log (1 / η) ≤ k ∧ (k : ℝ) ≤ C * Real.log (1 / η) ∧
          (∀ x ∈ Set.Icc (0 : ℝ) 1,
            0 ≤ (majorityPoly k).eval x ∧ (majorityPoly k).eval x ≤ 1) ∧
          MajorityApprox k η ∧
          (∀ j : ℕ, (j < majorityThreshold k ∨ k < j) → (majorityPoly k).coeff j = 0) ∧
          ∑ j ∈ Finset.Icc (majorityThreshold k) k, |(majorityPoly k).coeff j| ≤ 3 ^ k := by sorry

end GaussMixHH
