-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_3_3
-- name    : MultiOmniRate.Lipschitz.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:23:16.076474+00:00
-- url     : https://prove2.me/theorems/d061d054-a1ab-452b-91f8-8cde36619410
-- title:
--   Lemma 3.3 — $w_{\ell,r}\in[-2,2]^K$, $2(K-1)/r$-Lipschitz from $\ell_1$ to $\ell_\infty$, and $\|w_{\ell,r}-w_{\ell',r}\|_\infty\le\frac{2(K-1)}{r}\|L_\ell-L_{\ell'}\|_\infty$
-- statement:
--   Let $K\ge2$ and $0<r\le1/2$. For a bounded loss $\ell\in\mathcal L_{\mathrm{All}}$ let $w_{\ell,r}(q)=\mathbb E_{z\sim\mathrm{Unif}(\Delta_K)}[\Delta\ell^{\mathrm{pr}}((1-r)q+rz)]$ be its smoothed decision weights and $L_\ell$ its Bayes risk. Then:
--
--   1. $w_{\ell,r}(q)\in[-2,2]^K$ for every $q\in\Delta_K$;
--   2. $\displaystyle\|w_{\ell,r}(q)-w_{\ell,r}(q')\|_\infty\le\frac{2(K-1)}{r}\|q-q'\|_1$ for all $q,q'\in\Delta_K$;
--   3. for any two bounded losses $\ell,\ell'$,
--   $$\|w_{\ell,r}-w_{\ell',r}\|_\infty\le\frac{2(K-1)}{r}\,\|L_\ell-L_{\ell'}\|_\infty ,$$
--   the sup norm of $L_\ell-L_{\ell'}$ being taken over $\Delta_K$.
--
--   The third bound turns a cover of Bayes risks into a cover of smoothed decision weights (Lemma 3.11); the second makes the weights continuous, which Algorithm 1's minimizer needs.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - reading: "each $w_{\ell,r}$", "any two bounded losses" → $\ell,\ell'\in\mathcal L_{\mathrm{All}}$ (bounded, measurable in the action, measurable best response); reason: $w_{\ell,r}$ is an expectation, defined for the paper's losses with measurable best responses
--   - encoding: Lipschitz from $\ell_1$ to $\ell_\infty$; $\|w-w'\|_\infty\le\frac{2(K-1)}{r}\|L_\ell-L_{\ell'}\|_\infty$ → coordinatewise bounds for every $k$; the sup norm of $L_\ell-L_{\ell'}$ as any $c$ bounding $|L_\ell(p)-L_{\ell'}(p)|$ on $\Delta_K$; reason: equivalent formulations of the same norms
--   - encoding: $\mathrm{Unif}(\Delta_K)$ → `unifSimplex K`: normalized Lebesgue measure on the free coordinates $(p_1,\dots,p_{K-1})$, pushed to $\Delta_K$; reason: the uniform distribution on the simplex, as in the proof of Lemma 3.3 (App. A.1)
--   - encoding: $\mathcal L_{\mathrm{All}}$: arbitrary action spaces → `AllLoss.{u} K`: action spaces in a universe `u`, with a measurable structure; reason: $w_{\ell,r}$ and the Decision-OI term depend on $\ell$ only through $\ell^{\mathrm{pr}}$, which is itself a loss on $\Delta_K$, so every universe gives the same class
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 26, Lemma 3.3 (proof: p. 54, App. A.1)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_3_3.{u} {K : ℕ} [NeZero K] (hK : 2 ≤ K) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    (∀ (ℓ : AllLoss.{u} K) (q : Simplex K) (k : Fin K), |smoothW r ℓ.ℓ.pr q k| ≤ 2) ∧
    (∀ (ℓ : AllLoss.{u} K) (q q' : Simplex K) (k : Fin K),
      |smoothW r ℓ.ℓ.pr q k - smoothW r ℓ.ℓ.pr q' k| ≤
        2 * ((K : ℝ) - 1) / r * l1 ((q : Fin K → ℝ) - (q' : Fin K → ℝ))) ∧
    (∀ (ℓ ℓ' : AllLoss.{u} K) (c : ℝ),
      (∀ p : Simplex K, |bayesRisk ℓ.ℓ.loss p - bayesRisk ℓ'.ℓ.loss p| ≤ c) →
      ∀ (q : Simplex K) (k : Fin K),
        |smoothW r ℓ.ℓ.pr q k - smoothW r ℓ'.ℓ.pr q k| ≤ 2 * ((K : ℝ) - 1) / r * c) := by sorry

end MultiOmniRate.Lipschitz
