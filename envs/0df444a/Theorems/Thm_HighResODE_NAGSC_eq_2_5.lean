-- Prove2me | Theorems.Thm_HighResODE_NAGSC_eq_2_5
-- name    : HighResODE.NAGSC.eq_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:37.604225+00:00
-- url     : https://prove2.me/theorems/6d20b415-d346-4c8a-a1f8-ce83ba8f6e4a
-- title:
--   (2.5), p. 11 — phase-space representation of NAG-SC
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, let $s>0$ and $\mu s<1$, and let $(x_k,y_k)_{k\ge0}$ be a run of NAG-SC (1.3): $x_0=y_0$, $y_{k+1}=x_k-s\nabla f(x_k)$, $x_{k+1}=y_{k+1}+\frac{1-\sqrt{\mu s}}{1+\sqrt{\mu s}}(y_{k+1}-y_k)$. With the velocity $v_k=(x_{k+1}-x_k)/\sqrt s$, for every $k\ge1$,
--   $$x_k-x_{k-1}=\sqrt s\,v_{k-1},$$
--   $$v_k-v_{k-1}=-\frac{2\sqrt{\mu s}}{1-\sqrt{\mu s}}v_k-\sqrt s\big(\nabla f(x_k)-\nabla f(x_{k-1})\big)-\frac{1+\sqrt{\mu s}}{1-\sqrt{\mu s}}\cdot\sqrt s\,\nabla f(x_k),$$
--   and the initial velocity is
--   $$v_0=-\frac{2\sqrt s}{1+\sqrt{\mu s}}\nabla f(x_0).$$
--
--   This rewriting of NAG-SC as explicit position and velocity updates is what suggests the discrete Lyapunov function (2.6).
--
--   **Formalization Note** The two updates are stated for $k+1$ in place of $k$ (so for every $k\ge0$), avoiding natural-number subtraction. The page uses $\mu s<1$ implicitly (it divides by $1-\sqrt{\mu s}$); it is an explicit hypothesis here, together with $s>0$. No assumption on $f$ is needed: the identities are algebraic consequences of (1.3).
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 11, (2.5) and the initial velocity

import Mathlib
import Definitions.Def_HighResODE_NAGSC_FunctionClass
import Definitions.Def_HighResODE_NAGSC_Setting

namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- (2.5), p. 11: the phase-space representation of NAG-SC. With `v_k = (x_{k+1} − x_k)/√s`,
for every `k ≥ 1`: `x_k − x_{k−1} = √s v_{k−1}` and
`v_k − v_{k−1} = −(2√(μs)/(1 − √(μs))) v_k − √s(∇f(x_k) − ∇f(x_{k−1}))
  − ((1 + √(μs))/(1 − √(μs))) √s∇f(x_k)`; the initial velocity is
`v₀ = −(2√s/(1 + √(μs)))∇f(x₀)`. Stated with `k + 1` in place of `k`. -/
theorem eq_2_5 {n : ℕ} (f : E n → ℝ) (μ s : ℝ) (x y : ℕ → E n)
    (hrun : IsNAGSC f μ s x y) (hs : 0 < s) (hμs : μ * s < 1) :
    (∀ k : ℕ, x (k + 1) - x k = Real.sqrt s • vel s x k ∧
      vel s x (k + 1) - vel s x k =
        -(2 * Real.sqrt (μ * s) / (1 - Real.sqrt (μ * s))) • vel s x (k + 1)
          - Real.sqrt s • (gradient f (x (k + 1)) - gradient f (x k))
          - ((1 + Real.sqrt (μ * s)) / (1 - Real.sqrt (μ * s))) •
              (Real.sqrt s • gradient f (x (k + 1)))) ∧
    vel s x 0 = -(2 * Real.sqrt s / (1 + Real.sqrt (μ * s))) • gradient f (x 0) := by sorry

end HighResODE.NAGSC
