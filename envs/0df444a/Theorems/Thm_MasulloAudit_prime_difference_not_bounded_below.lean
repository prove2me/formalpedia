-- Prove2me | Theorems.Thm_MasulloAudit_prime_difference_not_bounded_below
-- name    : MasulloAudit.prime_difference_not_bounded_below
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:15:07.549961+00:00
-- url     : https://prove2.me/theorems/4442f9fe-156f-4ed9-9f67-e42b883cbb55
-- title:
--   The one-prime difference operator $f\mapsto f-f(\cdot-\ell)$ is not bounded below on $L^2(\mathbb R,(1+u^2)^{s/2}du)$
-- statement:
--   **Setting.** Fix a real number $s\ge 0$ and let $\mu_s$ be the measure $(1+u^2)^{s/2}\,du$ on $\mathbb R$. The space $L^2(\mathbb R,\mu_s)$ carries the norm
--
--   $$\|f\|_{s,2}^2=\int_{\mathbb R}|f(u)|^2\,(1+u^2)^{s/2}\,du .$$
--
--   This is the Sobolev norm (9.1.2.3) of the manuscript, $\|f\|_{s,2}^2=\int_G|f(g)|^2(1+|\log|g|_G|^2)^{s/2}\,d\mu_G(g)$, for functions of the module alone, written in the coordinate $u=\log|g|$. For $F=\mathbb Q$ it is the norm of $W^{s,2}(C_{\mathbb Q})$ on the functions invariant under $C^1_{\mathbb Q}$ (the trivial $C_F^1$-isotype). In this coordinate the one-prime operator $P_v\colon\varphi\mapsto\varphi(x)-\varphi(\pi_v^{-1}x)$ of the proof of Proposition 11.2.0.1 is the difference operator
--
--   $$(D_\ell f)(u)=f(u)-f(u-\ell),\qquad |\ell|=\log p .$$
--
--   The statement below allows either sign of $\ell$, so it does not depend on the sign convention for the translation.
--
--   **Statement.** For every real $s\ge 0$, every real $\ell\neq 0$ and every $c>0$ there is a function $f\in L^2(\mathbb R,\mu_s)$ such that
--
--   $$\|D_\ell f\|_{s,2}<c\,\|f\|_{s,2}.$$
--
--   The strict inequality forces $\|f\|_{s,2}>0$. Hence $D_\ell$ is **not bounded below** on $L^2(\mathbb R,\mu_s)$: there is no constant $\kappa>0$ with $\|D_\ell f\|_{s,2}\ge\kappa\|f\|_{s,2}$ for all $f$. The witness used in the proof is the indicator $f=\mathbf 1_{(0,N|\ell|]}$ with $N$ large, for which $\|D_\ell f\|_{s,2}^2/\|f\|_{s,2}^2=O(1/N)$.
--
--   **Bearing on the manuscript.** Proposition 11.2.0.1(2) and the paragraph before it (p. 484) assert that, for $s\ge 2|S_0|$, the extension by continuity of $P_{V_{S_0}}$ to the Hardy–Sobolev completion "remains a linear topological embedding with closed range". A linear topological embedding of normed spaces is bounded below. For a single finite place ($|S_0|=1$, so $s\ge 2$ is allowed) and the trivial $C^1_F$-isotype over $F=\mathbb Q$, the present theorem shows that the operator is not bounded below, for every $s\ge0$. This refutes the "topological embedding" part of the printed assertion in this model. The formal statement here does not include injectivity of $D_\ell$ or the non-closedness of its range; those are separate statements (an injective bounded operator between Banach spaces has closed range if and only if it is bounded below). This is an audit fact about one printed proposition, not a statement about the Riemann Hypothesis.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Proposition 11.2.0.1(2) and the paragraph preceding (11.2.0.3), pp. 484-485; norm (9.1.2.3), Definition 9.1.2.1, p. 399

import Mathlib

set_option autoImplicit false

open MeasureTheory

theorem MasulloAudit.prime_difference_not_bounded_below (s ℓ c : ℝ) (hs : 0 ≤ s) (hℓ : ℓ ≠ 0) (hc : 0 < c) :
    ∃ f : ℝ → ℂ,
      MemLp f 2 (volume.withDensity fun u : ℝ => ENNReal.ofReal ((1 + u ^ 2) ^ (s / 2))) ∧
      eLpNorm (fun u => f u - f (u - ℓ)) 2
          (volume.withDensity fun u : ℝ => ENNReal.ofReal ((1 + u ^ 2) ^ (s / 2))) <
        ENNReal.ofReal c *
          eLpNorm f 2 (volume.withDensity fun u : ℝ => ENNReal.ofReal ((1 + u ^ 2) ^ (s / 2))) := by sorry
