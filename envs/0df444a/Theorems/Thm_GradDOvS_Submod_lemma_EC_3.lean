-- Prove2me | Theorems.Thm_GradDOvS_Submod_lemma_EC_3
-- name    : GradDOvS.Submod.lemma_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:56.814347+00:00
-- url     : https://prove2.me/theorems/f18d416f-10c3-4b86-ace5-51d6737a182a
-- title:
--   Lemma EC.3, p. ec4 (PDF 42) (probability bound) — the martingale-difference terms of truncated SSGD average to O(√(dσ²/T·log(1/δ)))
-- statement:
--   Assume the standing assumptions ($d \ge 1$, $f$ submodular, $|f(A)-f(B)|\le L$), Assumption 1 with $\sigma > 0$, and let $x^* = \mathbb 1_{A^*}$ with $A^*$ a minimizer of $f$. Run Algorithm 2 from $x^0 = \mathbb 1_{A_0}$ with any step size $\eta$, and let
--   $$X_t = \langle g^t + b^t - \tilde g^t,\ x^t - x^*\rangle, \qquad t = 0,\dots,T-1,$$
--   where $g^t$ is the vector (3) at $x^t$, $b^t = b(x^t)$ the truncation bias and $\tilde g^t = T_M(\hat g^t)$. If $\epsilon > 0$, $\delta > 0$ and
--   $$M \ge \max\Big\{L,\ 2\sigma\sqrt{\log\frac{4\sigma dT}{\epsilon}}\Big\}, \qquad T \ge \frac{2\epsilon}{\sigma},$$
--   then with probability at least $1-\delta$
--   $$\frac1T\sum_{t=0}^{T-1} X_t \le \sqrt{\frac{224 d\sigma^2}{T}\log\frac1\delta}.$$
--
--   This controls the noise term in the proof of Theorem 2.
--
--   **Formalization Note** The printed choice $M = \max\{\cdot\}$ is relaxed to $M \ge \max\{\cdot\}$ (a stronger statement). The bias $b^t$ is $\mathbb E[T_M(\hat g)] - g$ at the current iterate (see Lemma EC.2). The martingale-difference property, also asserted on the page, is a step towards this bound and is not stated separately. The step size is arbitrary, as on the page.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. ec4 (PDF 42), Lemma EC.3

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Lemma EC.3, p. ec4 (PDF 42), probability bound: for the iterates `x^t` of Algorithm 2 (any step
size `η`) and a minimizer `x* = ind A*` of `f`, the terms `X_t = ⟨g^t + b^t - g̃^t, x^t - x*⟩`
satisfy `(1/T) ∑_{t<T} X_t ≤ √(224 d σ²/T · log(1/δ))` with probability at least `1 - δ`, when
`M ≥ max{L, 2σ√log(4σdT/ε)}` and `T ≥ 2ε/σ`. -/
theorem lemma_EC_3 {Ω : Type*} [MeasurableSpace Ω] {d T n : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Finset (Fin d) → ℝ) (L : ℝ) (σ : NNReal)
    (Z : Slot d T n → Ω → Finset (Fin d) → ℝ) (hZ : IsSimOracle P f σ Z)
    (hf : Standing L f) (hσ : 0 < σ) (ε δ η M : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hT : 2 * ε / (σ : ℝ) ≤ T)
    (hM : max L (2 * (σ : ℝ) * Real.sqrt (Real.log (4 * σ * d * T / ε))) ≤ M)
    (A₀ Astar : Finset (Fin d)) (hAstar : f Astar = minf f) :
    P {ω | Real.sqrt (224 * d * (σ : ℝ) ^ 2 / T * Real.log (1 / δ)) <
        (1 / (T : ℝ)) * ∑ t : Fin T, mdsTerm P Z f η M A₀ Astar t ω} ≤ ENNReal.ofReal δ
    := by sorry

end GradDOvS.Submod
