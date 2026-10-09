-- Prove2me | Theorems.Thm_LookbackMOT_HL_azema_yor
-- name    : LookbackMOT.HL.azema_yor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:55.821699+00:00
-- url     : https://prove2.me/theorems/6359c92f-d884-4847-a922-94b11a5deb28
-- title:
--   §3.4, p. 18 — Azéma–Yor: τ* ∈ 𝒯_∞, X_{τ*} ∼ μ and X*_{τ*} ∼ μ^HL
-- statement:
--   Let $B$ be an $(\mathcal F_t)$-Brownian motion and $X=X_0+B$, let $\mu$ be an integrable probability measure on $\mathbb R$ with mean $X_0$, barycenter function $b$ (3.9) and Hardy–Littlewood transform $\mu^{HL}$, and let
--   $$\tau^*=\inf\{t>0:\ X^*_t\ge b(X_t)\}$$
--   be the Azéma–Yor stopping time (3.13). Then
--   1. $\tau^*\in\mathcal T_\infty$: it is an a.s. finite stopping time and $(X_{t\wedge\tau^*})_{t\ge0}$ is a uniformly integrable martingale;
--   2. $X_{\tau^*}\sim\mu$;
--   3. $X^*_{\tau^*}\sim\mu^{HL}$.
--
--   The first two items say that $\tau^*$ solves the Skorokhod embedding problem for $\mu$; the third identifies the law of the maximum at the embedding. Together they give the lower bound of Section 3.4. The paper cites Azéma and Yor for them.
--
--   **Formalization Note** $\tau^*$ takes the value $+\infty$ when the defining set is empty; item 1 includes that this happens with probability $0$, so $X_{\tau^*}$ is not a junk value. The laws are stated as image measures of $P$ (Mathlib's `HasLaw`).
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 18, §3.4 (Azéma and Yor [1, 2]), with (3.13), p. 12

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem azema_yor {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ) (hB : IsFBrownian P ℱ B)
    (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (ν : Measure ℝ) (hν : IsHLTransform μ ν) :
    IsUIStop P ℱ (shift X₀ B) (tauStar B X₀ μ) ∧
      HasLaw (stoppedValue (shift X₀ B) (tauStar B X₀ μ)) μ P ∧
      HasLaw (runMaxUpTo (shift X₀ B) (tauStar B X₀ μ)) ν P := by sorry

end LookbackMOT.HL
