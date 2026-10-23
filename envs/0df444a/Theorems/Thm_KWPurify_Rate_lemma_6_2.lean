-- Prove2me | Theorems.Thm_KWPurify_Rate_lemma_6_2
-- name    : KWPurify.Rate.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:53.316053+00:00
-- url     : https://prove2.me/theorems/f8667242-2aec-4386-8887-40e75e1fbad2
-- title:
--   Lemma 6.2 (corrected: $0 \le c \le 1$) — $\binom{K}{M}^{-1}\sum_{R=M}^K\binom{R}{M}z^{K-R} \to 1/(1-(1-c)z)$ as $M/K \to c$
-- statement:
--   For natural numbers $M \le K$ and $z \in \mathbb C$ let
--   $$\Phi(K,M,z) = \binom{K}{M}^{-1}\sum_{R=M}^{K}\binom{R}{M} z^{K-R}.$$
--   Let $|z| < 1$ and $0 \le c \le 1$, and let $(K_j)$, $(M_j)$ be sequences of natural numbers with $M_j \le K_j$, $M_j \to \infty$, $K_j \to \infty$ and $M_j/K_j \to c$. Then
--   $$\lim_{j\to\infty}\Phi(K_j,M_j,z) = \frac{1}{1-(1-c)z}.$$
--
--   In the proof of the rate formula this is applied with $K = 2s$, $z = e^{-2\beta}$ and $c = \mu/\lambda$, to evaluate the binomial-sum branch of $f_{\mathrm{all}}$ at the dominant spin.
--
--   **Formalization Note** Corrected statement: the paper writes "$c \ge 1$", but $M \le K$ forces $M/K \le 1$, and the lemma is used with $c = \mu/\lambda < 1$; the correct range is $0 \le c \le 1$. The limit "$M,K\to\infty$, $M/K\to c$" is taken along arbitrary sequences.
-- source:
--   Keyl & Werner, The Rate of Optimal Purification procedures, arXiv:quant-ph/9910124v1, pp. 21–22, Lemma 6.2 (range of c corrected to 0 ≤ c ≤ 1)

import Mathlib
import Definitions.Def_KWPurify_Rate_Blocks

open Filter Topology

namespace KWPurify.Rate
theorem lemma_6_2 (z : ℂ) (hz : ‖z‖ < 1) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (K M : ℕ → ℕ) (hMK : ∀ j, M j ≤ K j)
    (hM : Tendsto M atTop atTop) (hK : Tendsto K atTop atTop)
    (hc : Tendsto (fun j => (M j : ℝ) / (K j : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun j => binomRatioSum (K j) (M j) z) atTop
      (𝓝 (1 / (1 - (1 - (c : ℂ)) * z))) := by sorry
end KWPurify.Rate
