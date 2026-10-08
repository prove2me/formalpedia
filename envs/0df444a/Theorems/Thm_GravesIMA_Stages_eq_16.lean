-- Prove2me | Theorems.Thm_GravesIMA_Stages_eq_16
-- name    : GravesIMA.Stages.eq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:54.958122+00:00
-- url     : https://prove2.me/theorems/711211bb-a22d-48f1-96f8-0d72e82e7978
-- title:
--   (16), p. 57 — for t ≥ K the upstream inventory y_t is N(y₀, σ²Σ_{i=0}^{K−1}(1 + (L + i)α)²)
-- statement:
--   Throughout, time is indexed by the integers, $0\le\alpha\le1$, and $(d_t, F_t, q_t, x_t)$ is the single-stage system of Graves (1999, §2) driven by a shock sequence $(\varepsilon_t)_{t\ge1}$: demand $d_1=\mu+\varepsilon_1$, $d_t=d_{t-1}-(1-\alpha)\varepsilon_{t-1}+\varepsilon_t$ for $t\ge2$; the exponentially weighted moving-average forecast $F_1=\mu$, $F_{t+1}=\alpha d_t+(1-\alpha)F_t$; orders $q_t=\mu$ for $t\le0$ and $q_t=d_t+L(F_{t+1}-F_t)$ for $t\ge1$ with lead time $L\in\mathbb N$; inventory $x_t=x_{t-1}-d_t+q_{t-L}$ for $t\ge1$, with the initial inventory $x_0$ free. The two-stage system of §3 adds an upstream stage with lead time $K\in\mathbb N$ that sees the orders $q_t$ as its demand: forecast $G_1=\mu$, $G_{t+1}=\beta q_t+(1-\beta)G_t$ with $\beta=\alpha/(1+L\alpha)$; orders $p_t=\mu$ for $t\le0$ and $p_t=q_t+K(G_{t+1}-G_t)$ for $t\ge1$; inventory $y_t=y_{t-1}-q_t+p_{t-K}$ for $t\ge1$, with $y_0$ free.
--
--   The shocks $\varepsilon_t$, $t\ge1$, are random variables on a probability space $(\Omega,P)$; they are measurable, mutually independent, and each has law $N(0,\sigma^2)$. The system equations hold for every outcome $\omega$, and the initial inventory is a deterministic constant. The upstream initial inventory $y_0$ is a constant.
--
--   Then for every period $t\ge\max(1,K)$, the upstream inventory $y_t$ is normally distributed with
--   $$\mathbb E[y_t]=y_0,\qquad \operatorname{Std}[y_t]=\sigma\sqrt{\sum_{i=0}^{K-1}\bigl(1+(L+i)\alpha\bigr)^2}. \tag{16}$$
--
--   The standard deviation of $y_t$ measures the upstream safety-stock requirement. It depends on the downstream lead time $L$ as well as on the upstream lead time $K$ whenever $\alpha>0$.
--
--   **Formalization Note** Independence is `iIndepFun` of the family $(\varepsilon_t)_{t\ge1}$ indexed by the subtype $\{s\in\mathbb Z: s\ge1\}$; shocks at $t\le0$ are never read by the model. "Normally distributed with mean $m$ and standard deviation $s$" is the law equality `P.map X = gaussianReal m (s²)`; the variance is passed as `Real.toNNReal` of a sum of squares times $\sigma^2$, which is nonnegative, so no clipping occurs. Each $\varepsilon_t$ is assumed measurable, so the pushforward measures are genuine laws.
-- source:
--   Graves, A single-item inventory model for a nonstationary demand process, Manuf. Serv. Oper. Manag. 1(1) (1999), p. 57, (16)

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model
open MeasureTheory ProbabilityTheory

namespace GravesIMA.Stages

theorem eq_16 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σ : ℝ) (ε : ℤ → Ω → ℝ) (hmeas : ∀ t, Measurable (ε t))
    (hind : iIndepFun (fun t : {s : ℤ // 1 ≤ s} => ε t) P)
    (hlaw : ∀ t : ℤ, 1 ≤ t → P.map (ε t) = gaussianReal 0 (Real.toNNReal (σ ^ 2)))
    (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L K : ℕ) (d F q x G p y : ℤ → Ω → ℝ)
    (hsys : ∀ ω, IsTwoStage μ α L K (fun s => ε s ω) (fun s => d s ω) (fun s => F s ω)
      (fun s => q s ω) (fun s => x s ω) (fun s => G s ω) (fun s => p s ω) (fun s => y s ω))
    (y0 : ℝ) (hy0 : ∀ ω, y 0 ω = y0) (t : ℤ) (ht1 : 1 ≤ t) (htK : (K : ℤ) ≤ t) :
    P.map (y t) = gaussianReal y0
      (Real.toNNReal (σ ^ 2 * ∑ i ∈ Finset.range K, (1 + ((L : ℝ) + i) * α) ^ 2)) := by sorry

end GravesIMA.Stages
