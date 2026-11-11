-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_3_11
-- name    : MultiOmniRate.Lipschitz.lemma_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:23:24.342755+00:00
-- url     : https://prove2.me/theorems/4d703421-9ba7-45f1-9d48-72e31c936bec
-- title:
--   Lemma 3.11 — two covering bounds for $\{w_{\ell,r}:\ell\in\mathcal L_{\mathrm{All}}\}$ ($K\ge3$ and $K=2$)
-- statement:
--   Let $M(u)$ be the size of the smallest uniform $u$-cover of the smoothed decision weights $\{w_{\ell,r}:\ell\in\mathcal L_{\mathrm{All}}\}$. For every $0<r\le1/2$ and $0<u\le1$:
--
--   1. for $K\ge3$, with $C_K$ depending only on $K$,
--   $$\log(2M(u))\le C_K\min\Big\{(ru)^{-(K-1)/2},\ \frac1u(ru)^{-(K-2)/2}\Big\}\qquad(3.3);$$
--   2. for $K=2$, with an absolute constant $C$,
--   $$\log(2M(u))\le C\min\Big\{(ru)^{-1/2},\ \frac1u\log\frac{C}{ru}\Big\}.$$
--
--   These bounds, summed over dyadic accuracies, give the decision learner's regret (Lemma 3.14).
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - encoding: $M(u)$, the size of the smallest uniform $u$-cover → existence of a uniform $u$-cover $\mathcal B$ with $\log(2|\mathcal B|)$ below the bound; reason: the smallest cover is no larger than $\mathcal B$, and $\log(2\cdot)$ is increasing; the two forms are equivalent
--   - encoding: $\mathrm{Unif}(\Delta_K)$ → `unifSimplex K`: normalized Lebesgue measure on the free coordinates $(p_1,\dots,p_{K-1})$, pushed to $\Delta_K$; reason: the uniform distribution on the simplex, as in the proof of Lemma 3.3 (App. A.1)
--   - encoding: $\mathcal L_{\mathrm{All}}$: arbitrary action spaces → `AllLoss.{u} K`: action spaces in a universe `u`, with a measurable structure; reason: $w_{\ell,r}$ and the Decision-OI term depend on $\ell$ only through $\ell^{\mathrm{pr}}$, which is itself a loss on $\Delta_K$, so every universe gives the same class
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 29, Lemma 3.11 (proof of the second bound: pp. 55–57, App. A.2.2)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_Smoothing

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_3_11.{u} :
    (∀ (K : ℕ) [NeZero K], 3 ≤ K → ∃ C : ℝ, 0 < C ∧
      ∀ r u : ℝ, 0 < r → r ≤ 1 / 2 → 0 < u → u ≤ 1 →
        ∃ B : Finset (Simplex K → Fin K → ℝ), IsUniformCover B (smoothWClass.{u} K r) u ∧
          Real.log (2 * (B.card : ℝ)) ≤
            C * min ((r * u) ^ (-((K : ℝ) - 1) / 2)) (1 / u * (r * u) ^ (-((K : ℝ) - 2) / 2))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ r u : ℝ, 0 < r → r ≤ 1 / 2 → 0 < u → u ≤ 1 →
        ∃ B : Finset (Simplex 2 → Fin 2 → ℝ), IsUniformCover B (smoothWClass.{u} 2 r) u ∧
          Real.log (2 * (B.card : ℝ)) ≤
            C * min ((r * u) ^ (-(1 / 2 : ℝ))) (1 / u * Real.log (C / (r * u)))) := by sorry

end MultiOmniRate.Lipschitz
