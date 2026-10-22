-- Prove2me | Theorems.Thm_GradDOvS_Submod_lemma_EC_2
-- name    : GradDOvS.Submod.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:56.977619+00:00
-- url     : https://prove2.me/theorems/95b55a1d-dafe-4cb1-ae12-60c8e73ed036
-- title:
--   Lemma EC.2, p. ec3 (PDF 41) (corrected truncation level) — the truncation bias has ℓ1 norm at most ε/(2T)
-- statement:
--   Let $f$ satisfy $|f(A) - f(B)| \le L$ for all $A, B$, let the oracle satisfy Assumption 1 with $\sigma > 0$, $d \ge 1$, $\epsilon > 0$, and let $T$ and $M$ satisfy
--   $$T \ge \frac{2\epsilon}{\sigma}, \qquad M \ge L + 2\sigma\sqrt{\log\frac{4\sigma d T}{\epsilon}}.$$
--   Then for every iteration $t < T$ and every point $x$, the bias $b(x) = \mathbb E[T_M(\hat g^t(x))] - g(x)$ of the truncated estimator (4) at $x$ satisfies
--   $$\|b(x)\|_1 \le \frac{\epsilon}{2T}.$$
--
--   In Algorithm 2 the bias of step $t$, $b^t = \mathbb E[\tilde g^t \mid x^0,\dots,x^t] - g^t$, equals $b(x^t)$ because the slots of iteration $t$ are independent of $x^0,\dots,x^t$; this lemma therefore bounds every $\|b^t\|_1$.
--
--   **Formalization Note** The bias is the page's $b_t = \mathbb E[\tilde g^t \mid x^0,\dots,x^t] - g^t$ with $\tilde g^t = T_M(\hat g^t)$, evaluated at a fixed point. One correction: the printed hypothesis $M \ge 2\sigma\sqrt{\log(4\sigma dT/\epsilon)}$ does not suffice. For $d = 1$, $\sigma = 1$, Gaussian noise, $\epsilon = 0.1$, $T = 100$, $M = 2\sqrt{\log 4000} \approx 5.760$, $f(\emptyset) = 0$, $f(\{1\}) = M$ (so $L = M$), the truncated estimate is $\mathrm{clip}(M + Y, -M, M)$ with $Y \sim N(0,2)$, whose bias is $-\mathbb E[Y^-] \approx -0.564$, while $\epsilon/(2T) = 0.0005$ (the proof truncates the noise $Y_1+Y_2$ instead of $g + Y_1 + Y_2$). The truncation level is raised by $L$. Submodularity is not needed and not assumed.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. ec3 (PDF 41), Lemma EC.2 and the definition of b_t before it (corrected; see Formalization Note)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Lemma EC.2, p. ec3 (PDF 41), corrected truncation level `M ≥ L + 2σ√log(4σdT/ε)` (the printed
`M ≥ 2σ√log(4σdT/ε)` does not suffice): at every point `x`, the bias `E[T_M(ĝ)] - g` of the truncated
estimator of iteration `t` has `ℓ₁` norm at most `ε/(2T)`. -/
theorem lemma_EC_2 {Ω : Type*} [MeasurableSpace Ω] {d T n : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Finset (Fin d) → ℝ) (L : ℝ) (σ : NNReal)
    (Z : Slot d T n → Ω → Finset (Fin d) → ℝ) (hZ : IsSimOracle P f σ Z)
    (hd : 1 ≤ d) (hL : ∀ A B : Finset (Fin d), |f A - f B| ≤ L) (hσ : 0 < σ)
    (ε M : ℝ) (hε : 0 < ε) (hT : 2 * ε / (σ : ℝ) ≤ T)
    (hM : L + 2 * (σ : ℝ) * Real.sqrt (Real.log (4 * σ * d * T / ε)) ≤ M)
    (t : Fin T) (x : Fin d → ℝ) :
    ∑ j, |truncBias P Z f M t x j| ≤ ε / (2 * T) := by sorry

end GradDOvS.Submod
