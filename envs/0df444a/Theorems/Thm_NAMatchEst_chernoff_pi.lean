-- Prove2me | Theorems.Thm_NAMatchEst_chernoff_pi
-- name    : NAMatchEst.chernoff_pi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T00:23:45.663834+00:00
-- url     : https://prove2.me/theorems/1155befd-08de-41d2-b8e5-583be435a2b3
-- title:
--   Chernoff bound (moment-generating-function form) for product distributions
-- statement:
--   Let $Q$ be a finite set and let $\omega=(\omega_1,\dots,\omega_m)$ be a random vector with **independent** coordinates, $\omega_i$ distributed according to a probability distribution $p_i$ on $Q$. For each $i$ let $f_i : Q\to[0,1]$ and put
--   $$X(\omega)=\sum_{i=1}^m f_i(\omega_i),\qquad \mathbb E[X]=\sum_{i=1}^m\sum_{q\in Q}p_i(q)f_i(q).$$
--   Suppose $\lambda_L\le\mathbb E[X]\le\lambda_H$. Then for every $t\ge0$ and every real threshold $a$,
--   $$\Pr[X\ge a]\le\exp\big(\lambda_H(e^{t}-1)-ta\big),\qquad \Pr[X\le a]\le\exp\big(\lambda_L(e^{-t}-1)+ta\big).$$
--
--   These are the two moment-generating-function bounds from which the usual multiplicative Chernoff bounds (Proposition 2.1 of the source paper) follow by choosing $t$; keeping $t$ free makes them convenient for the binomial tail computations of the sampling tests (first-layer degree test, residual-total test, pilot, right-endpoint certification, sample-size caps).
--
--   **Formalization Note** The law of $\omega$ is the product distribution `RandomQueryXOR.piDist p` on `Fin m → Q` (a `WildeQIT.FinDist`); probabilities are written as weighted sums of indicators over the finite sample space.
-- source:
--   Dubhashi–Panconesi, Concentration of Measure for the Analysis of Randomized Algorithms (CUP 2009), §1.2–1.3 (proof of Theorem 1.1, the Chernoff–Hoeffding bound via the moment generating function); used as the concentration tool behind Proposition 2.1 of Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation (STOC 2027 submission), p.13.

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_RandomQueryXOR_uniformOn

namespace NAMatchEst

theorem chernoff_pi {m : ℕ} {Q : Type} [Fintype Q] (p : Fin m → WildeQIT.FinDist Q)
    (f : Fin m → Q → ℝ) (hf : ∀ i q, 0 ≤ f i q ∧ f i q ≤ 1) (lamL lamH t a : ℝ)
    (hL : lamL ≤ ∑ i, ∑ q, (p i).prob q * f i q) (hH : ∑ i, ∑ q, (p i).prob q * f i q ≤ lamH)
    (ht : 0 ≤ t) :
    (∑ ω, (RandomQueryXOR.piDist p).prob ω * if a ≤ ∑ i, f i (ω i) then 1 else 0) ≤
        Real.exp (lamH * (Real.exp t - 1) - t * a) ∧
      (∑ ω, (RandomQueryXOR.piDist p).prob ω * if ∑ i, f i (ω i) ≤ a then 1 else 0) ≤
        Real.exp (lamL * (Real.exp (-t) - 1) + t * a) := by sorry

end NAMatchEst
