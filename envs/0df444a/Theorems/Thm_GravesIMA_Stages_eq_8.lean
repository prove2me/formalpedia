-- Prove2me | Theorems.Thm_GravesIMA_Stages_eq_8
-- name    : GravesIMA.Stages.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:51.149228+00:00
-- url     : https://prove2.me/theorems/9fc8a2a2-0662-44b1-ac8f-e7807b23db65
-- title:
--   (8), p. 53 — for t ≥ L, x_t is N(x₀, σ²Σ_{i<L}(1 + iα)²), and Σ_{i<L}(1+iα)² = L(1 + α(L−1) + α²(L−1)(2L−1)/6)
-- statement:
--   Throughout, time is indexed by the integers, $0\le\alpha\le1$, and $(d_t, F_t, q_t, x_t)$ is the single-stage system of Graves (1999, §2) driven by a shock sequence $(\varepsilon_t)_{t\ge1}$: demand $d_1=\mu+\varepsilon_1$, $d_t=d_{t-1}-(1-\alpha)\varepsilon_{t-1}+\varepsilon_t$ for $t\ge2$; the exponentially weighted moving-average forecast $F_1=\mu$, $F_{t+1}=\alpha d_t+(1-\alpha)F_t$; orders $q_t=\mu$ for $t\le0$ and $q_t=d_t+L(F_{t+1}-F_t)$ for $t\ge1$ with lead time $L\in\mathbb N$; inventory $x_t=x_{t-1}-d_t+q_{t-L}$ for $t\ge1$, with the initial inventory $x_0$ free.
--
--   The shocks $\varepsilon_t$, $t\ge1$, are random variables on a probability space $(\Omega,P)$; they are measurable, mutually independent, and each has law $N(0,\sigma^2)$. The system equations hold for every outcome $\omega$, and the initial inventory is a deterministic constant.
--
--   Then for every period $t\ge\max(1,L)$, the inventory $x_t$ is normally distributed with
--   $$\mathbb E[x_t]=x_0,\qquad \operatorname{Std}[x_t]=\sigma\sqrt{\sum_{i=0}^{L-1}(1+i\alpha)^2}=\sigma\sqrt L\sqrt{1+\alpha(L-1)+\frac{\alpha^2(L-1)(2L-1)}{6}} .$$
--
--   The second equality is stated as the identity of the quantities under the square roots, $\sum_{i=0}^{L-1}(1+i\alpha)^2=L\bigl(1+\alpha(L-1)+\alpha^2(L-1)(2L-1)/6\bigr)$; both sides are nonnegative, so it is equivalent to the equality of the standard deviations. The standard deviation of the inventory is the safety stock requirement of the system.
--
--   **Formalization Note** Independence is `iIndepFun` of the family $(\varepsilon_t)_{t\ge1}$ indexed by the subtype $\{s\in\mathbb Z: s\ge1\}$; shocks at $t\le0$ are never read by the model. "Normally distributed with mean $m$ and standard deviation $s$" is the law equality `P.map X = gaussianReal m (s²)`; the variance is passed as `Real.toNNReal` of a sum of squares times $\sigma^2$, which is nonnegative, so no clipping occurs. Each $\varepsilon_t$ is assumed measurable, so the pushforward measures are genuine laws.
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), p. 53, (8)

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model
open MeasureTheory ProbabilityTheory

namespace GravesIMA.Stages

theorem eq_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σ : ℝ) (ε : ℤ → Ω → ℝ) (hmeas : ∀ t, Measurable (ε t))
    (hind : iIndepFun (fun t : {s : ℤ // 1 ≤ s} => ε t) P)
    (hlaw : ∀ t : ℤ, 1 ≤ t → P.map (ε t) = gaussianReal 0 (Real.toNNReal (σ ^ 2)))
    (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L : ℕ) (d F q x : ℤ → Ω → ℝ)
    (hsys : ∀ ω, IsStage μ α L (fun s => ε s ω) (fun s => d s ω) (fun s => F s ω)
      (fun s => q s ω) (fun s => x s ω))
    (x0 : ℝ) (hx0 : ∀ ω, x 0 ω = x0) (t : ℤ) (ht1 : 1 ≤ t) (htL : (L : ℤ) ≤ t) :
    P.map (x t) =
        gaussianReal x0 (Real.toNNReal (σ ^ 2 * ∑ i ∈ Finset.range L, (1 + (i : ℝ) * α) ^ 2)) ∧
      ∑ i ∈ Finset.range L, (1 + (i : ℝ) * α) ^ 2 =
        (L : ℝ) * (1 + α * ((L : ℝ) - 1) + α ^ 2 * ((L : ℝ) - 1) * (2 * (L : ℝ) - 1) / 6) := by sorry

end GravesIMA.Stages
