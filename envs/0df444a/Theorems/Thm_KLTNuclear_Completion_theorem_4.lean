-- Prove2me | Theorems.Thm_KLTNuclear_Completion_theorem_4
-- name    : KLTNuclear.Completion.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:28.138518+00:00
-- url     : https://prove2.me/theorems/187ba880-b49e-4513-b353-119a0e952481
-- title:
--   Theorem 4 — uniform matrix completion with $|Y_i|\le\eta$: with probability $\ge1-e^{-t}$, (3.5) holds for all $A$
-- statement:
--   Let $n, m_1, m_2\ge1$ and $m=m_1+m_2$. Observe independent random pairs $(X_i,Y_i)$, $i=1,\dots,n$, following the trace regression model
--   $$\mathbb E(Y_i\mid X_i)=\operatorname{tr}(X_i^\top A_0),$$
--   where $A_0\in\mathbb R^{m_1\times m_2}$ is unknown and the $X_i$ are uniformly distributed on the matrix completion basis $\mathcal X=\{e_j(m_1)e_k^\top(m_2)\}$. Assume $\max_i|Y_i|\le\eta$ almost surely for some constant $\eta$. For $t>0$ let $\lambda>0$ satisfy
--   $$\lambda\ge4\eta\max\Big\{\sqrt{\frac{t+\log m}{(m_1\wedge m_2)n}},\ \frac{2(t+\log m)}{n}\Big\},\tag{3.6}$$
--   and let $\hat A^\lambda$ be the nuclear-norm penalized estimator (3.1), i.e. a minimizer over $\mathbb R^{m_1\times m_2}$ of
--   $$\frac1{m_1m_2}\|A\|_2^2-\Big\langle\frac2n\sum_{i=1}^nY_iX_i,A\Big\rangle+\lambda\|A\|_1 .$$
--   Then with probability at least $1-e^{-t}$, simultaneously for all $A\in\mathbb R^{m_1\times m_2}$,
--   $$\|\hat A^\lambda-A_0\|_2^2\le\|A-A_0\|_2^2+m_1m_2\min\Big\{2\lambda\|A\|_1,\ \Big(\frac{1+\sqrt2}{2}\Big)^2m_1m_2\lambda^2\operatorname{rank}(A)\Big\}.\tag{3.5}$$
--
--   This is the paper's oracle inequality for noisy matrix completion under uniform sampling with bounded responses. Taking $A=A_0$, $t\asymp\log m$ and $\lambda$ equal to the right-hand side of (3.6), in the regime where the first term of the maximum dominates, the bound reads $\|\hat A^\lambda-A_0\|_2^2/(m_1m_2)\lesssim\eta^2\,(m_1\vee m_2)\operatorname{rank}(A_0)\log(m)/n$.
--
--   **Formalization Note** The pairs are assumed independent (standing assumption, p. 1), each $X_i$ uniform on $\mathcal X$ (encoded by a uniform index $I_i$), the $Y_i$ measurable; integrability follows from boundedness. The model is the conditional expectation given the $\sigma$-algebra of $X_i$. $\lambda>0$ is the standing assumption of (1.6). The estimator $\hat A^\lambda(\omega)$ is any minimizer at each sample point (no measurability needed). "With probability at least $1-e^{-t}$ … for all $A$" is uniform in $A$: the outer measure of the set of $\omega$ at which (3.5) fails for some $A$ is at most $e^{-t}$. $\log$ is natural, $m_1\wedge m_2=\min(m_1,m_2)$.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 14, Theorem 4, (3.6), with (3.5) of Theorem 3 (p. 14) and (3.1) (p. 12); model (1.1), p. 1

import Mathlib
import Definitions.Def_KLTNuclear_Completion_Model

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace KLTNuclear.Completion

/-- Theorem 4, p. 14: let `X_i` be i.i.d. uniformly distributed on `𝒳` (the pairs `(X_i, Y_i)`
independent and following the trace regression model (1.1), p. 1), and `max_i |Y_i| ≤ η` almost
surely. For `t > 0` and `λ` satisfying (3.6),
`λ ≥ 4η max { √((t + log m)/((m₁ ∧ m₂) n)), 2(t + log m)/n }`, `m = m₁ + m₂`, with probability at
least `1 − e^{−t}` the estimator `Â^λ` of (3.1) satisfies (3.5),
`‖Â^λ − A₀‖₂² ≤ ‖A − A₀‖₂² + m₁m₂ min { 2λ‖A‖₁, ((1+√2)/2)² m₁m₂ λ² rank(A) }`,
for all `A ∈ ℝ^{m₁×m₂}` simultaneously: the outer measure of the set of `ω` at which (3.5) fails
for some `A` is at most `e^{−t}`. `Âω ω` is any minimizer of (3.1) at `ω`. -/
theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (I : Fin n → Ω → Fin m₁ × Fin m₂) (hI : ∀ i, UniformIndex P (I i))
    (Y : Fin n → Ω → ℝ) (hYmeas : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (fun i ω => (I i ω, Y i ω)) P)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P (designMatrix I) Y A₀)
    (η : ℝ) (hη : ∀ᵐ ω ∂P, ∀ i, |Y i ω| ≤ η) (t : ℝ) (ht : 0 < t)
    (lam : ℝ) (hlam : 0 < lam)
    (h36 : 4 * η * max
          (Real.sqrt ((t + Real.log ((m₁ + m₂ : ℕ) : ℝ)) / (((min m₁ m₂ : ℕ) : ℝ) * n)))
          (2 * (t + Real.log ((m₁ + m₂ : ℕ) : ℝ)) / n) ≤ lam)
    (Âω : Ω → RealMatrix m₁ m₂)
    (hÂ : ∀ ω, IsCompletionEstimator (designMatrix I) Y lam ω (Âω ω)) :
    P {ω | ∃ A : RealMatrix m₁ m₂, ¬ (frobeniusNormSq (Âω ω - A₀) ≤
        frobeniusNormSq (A - A₀) + (m₁ : ℝ) * m₂ *
          min (2 * lam * nuclearNorm A)
            (((1 + Real.sqrt 2) / 2) ^ 2 * ((m₁ : ℝ) * m₂) * lam ^ 2 * (A.rank : ℝ)))}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end KLTNuclear.Completion
