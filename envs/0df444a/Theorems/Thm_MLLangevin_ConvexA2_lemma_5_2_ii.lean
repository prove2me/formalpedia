-- Prove2me | Theorems.Thm_MLLangevin_ConvexA2_lemma_5_2_ii
-- name    : MLLangevin.ConvexA2.lemma_5_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:19.00178+00:00
-- url     : https://prove2.me/theorems/a2142f36-d0b3-45a3-bf0c-8e1311bc39ff
-- title:
--   Lemma 5.2 (ii), p. 30 — one-step error 𝔼|X^x_γ − X̄^y_γ|² ≤ |x − y|²e^{−αγ} + c_γ(x, y)γ³ for 𝒞² drifts
-- statement:
--   Assume $(\mathbf C_\alpha)$, that $b$ is $L$-Lipschitz with $0<\alpha\le L$ and $\mathcal C^2$ with bounded partial derivatives up to order 2, and $\sigma>0$. Let $W$ be a standard $d$-dimensional Brownian motion, $x,y\in\mathbb R^d$, and let $X^x$ solve $X^x_t=x+\int_0^tb(X^x_s)\,ds+\sigma W_t$; let $\bar X^y_t=y+t\,b(y)+\sigma W_t$ be one Euler step from $y$, driven by the same motion. Then for every $\gamma>0$,
--   $$\mathbb E\big[|X^x_\gamma-\bar X^y_\gamma|^2\big]\le|x-y|^2e^{-\alpha\gamma}+c_\gamma(x,y)\gamma^3,$$
--   with
--   $$c_\gamma(x,y)=\frac23\Big(\frac{L^2}{\alpha}|b(y)|^2+\frac{\sigma^4}{\alpha}\|\Delta b\|^2_{2,\infty}+\sigma L\|\nabla b\|_{2,\infty}\big(\sqrt\gamma\,S(x,\gamma)+\sigma\sqrt d\big)\Big),\qquad S(x,\gamma)=\sup_{u\in[0,\gamma]}\mathbb E[|b(X^x_u)|^2]^{1/2}.$$
--
--   This one-step bound, of order $\gamma^3$ instead of the $\gamma^2$ of Lemma 5.2(i), is what yields strong order one for the additive Euler scheme and hence the confluence exponent $\mathfrak a=2$.
--
--   **Formalization Note** The page states only "Let $\gamma>0$". The standing hypotheses of §5.1 ($(\mathbf C_\alpha)$, $L$-Lipschitz, $0<\alpha\le L$), the regularity of §2.4.2 (without which $\nabla b$ and $\Delta b$ are undefined) and $\sigma>0$ (§2.4) are carried as hypotheses. Both sides are in $[0,\infty]$, since $S(x,\gamma)$ may be infinite a priori. $\|\nabla b\|_{2,\infty}$ and $\|\Delta b\|^2_{2,\infty}$ follow the definitions of pp. 31–32.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Lemma 5.2 (ii), p. 30, with (18), p. 11, and pp. 31–32

import Mathlib
import Definitions.Def_MLLangevin_ConvexA2_Multilevel
import Definitions.Def_MLLangevin_ConvexA2_DriftNorms

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

theorem lemma_5_2_ii {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → SDEState d) (hW : IsStandardBrownian P W)
    (b : SDEState d → SDEState d) (L α σ : ℝ)
    (hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖) (hC : MLLangevin.ConvexA1.CondC b α) (hα : 0 < α) (hαL : α ≤ L)
    (hb2 : C2Bounded b) (hσ : 0 < σ)
    (x y : SDEState d) (X : ℝ≥0 → Ω → SDEState d) (hX : IsAddSolution b σ W x X)
    (γ : ℝ) (hγ : 0 < γ) :
    eLpNorm (fun ω => X γ.toNNReal ω - (y + γ • b y + σ • W γ.toNNReal ω)) 2 P ^ 2 ≤
      ENNReal.ofReal (‖x - y‖ ^ 2 * Real.exp (-α * γ))
        + ENNReal.ofReal (2 / 3 * γ ^ 3) *
          (ENNReal.ofReal (L ^ 2 / α * ‖b y‖ ^ 2 + σ ^ 4 / α * lapNormSq b)
            + ENNReal.ofReal (σ * L * gradNorm b) *
              (ENNReal.ofReal (Real.sqrt γ) * Sfun P b X γ + ENNReal.ofReal (σ * Real.sqrt d))) := by sorry

end MLLangevin.ConvexA2
