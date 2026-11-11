-- Prove2me | Theorems.Thm_MIBF_Balanced_lemma_4_7
-- name    : MIBF.Balanced.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:57:23.223191+00:00
-- url     : https://prove2.me/theorems/3be860da-4a6a-45e4-8c48-1980d2ea10ba
-- title:
--   Lemma 4.7 — uniqueness of the stationary contact: the system (26)–(27) has at most one solution with $0<u<w<1$
-- statement:
--   Let $\alpha,\beta\ge0$ with $\alpha+\beta>0$ and let $K_0,K_1\ge0$. Consider the system (natural logarithms)
--   $$f_1(u,w)=\alpha\ln u+\beta\ln w+\frac{(u-w)^2}{2uw}=K_1,$$
--   $$f_0(u,w)=\alpha\ln(1-u)+\beta\ln(1-w)+\frac{(u-w)^2}{2(1-u)(1-w)}=K_0 .$$
--   Then the system has at most one solution $(u,w)$ with $0<u<w<1$.
--
--   This is the uniqueness of the stationary contact used in the proof of the global contact-plane inequality (Theorem 4.6): a contact plane touching the cost at an interior point is determined by that point.
--
--   **Formalization Note** The coefficients printed as $a,b$ are named $\alpha,\beta$ in Lean, to keep them apart from the means $a,b$ elsewhere in the paper. "At most one solution" is `Set.Subsingleton` of the solution set in the open triangle $0<u<w<1$.
--
--   Differences from the source: none.
-- source:
--   Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, Woodruff, A Proof of the Most Informative Boolean Function Conjecture, arXiv:2609.24931 (held version, sha256 35793b82…1f9f), p. 13, Lemma 4.7, eqs. (26)–(27); proof in Appendix B

import Mathlib

namespace MIBF.Balanced
theorem lemma_4_7 (α β K0 K1 : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : 0 < α + β)
    (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1) :
    Set.Subsingleton {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧
      α * Real.log p.1 + β * Real.log p.2 + (p.1 - p.2) ^ 2 / (2 * p.1 * p.2) = K1 ∧
      α * Real.log (1 - p.1) + β * Real.log (1 - p.2)
        + (p.1 - p.2) ^ 2 / (2 * (1 - p.1) * (1 - p.2)) = K0} := by sorry
end MIBF.Balanced
