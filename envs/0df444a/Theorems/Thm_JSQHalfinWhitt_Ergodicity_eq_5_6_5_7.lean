-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Ergodicity_eq_5_6_5_7
-- name    : JSQHalfinWhitt.Ergodicity.eq_5_6_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:07.094725+00:00
-- url     : https://prove2.me/theorems/d01e96ca-158a-43a8-aef1-ea00af1c9b30
-- title:
--   Section 5.1, (5.6)–(5.7) — φ^{(ℓ,u)} has an absolutely continuous derivative with φ′(ℓ) = φ′(u) = 0, |φ′| ≤ 4/(u−ℓ), |φ″| ≤ 12/(u−ℓ)²
-- statement:
--   Let $\ell<u$ and let $\phi=\phi^{(\ell,u)}$ be the smoothed indicator (5.5), which is $0$ on $(-\infty,\ell]$, $1$ on $[u,\infty)$ and a piecewise cubic on $[\ell,u]$ with break point $(u+\ell)/2$. Then:
--
--   1. $\phi$ is differentiable on $\mathbb R$, and its derivative $\phi'$ is absolutely continuous on every bounded interval;
--   2. (5.6) $\phi'(\ell)=\phi'(u)=0$;
--   3. (5.7) for all $x$, and for all $x\notin\{\ell,(u+\ell)/2,u\}$ (where $\phi'$ is differentiable),
--   $$|\phi'(x)|\le\frac{4}{u-\ell},\qquad |\phi''(x)|\le\frac{12}{(u-\ell)^2}.$$
--
--   These bounds control the derivatives of the solutions $f^{(1)},f^{(2)}$ of the PDEs (5.9)–(5.10), and through them the error term of the generator comparison in the proof of Theorem 4.
--
--   **Formalization Note** $\phi'$ is `deriv φ` and $\phi''$ is `deriv (deriv φ)`. The second derivative does not exist at $\ell$, $(u+\ell)/2$ and $u$ (it jumps there), so the bound on $\phi''$ is stated, together with the differentiability of $\phi'$, at every other point; this is the reading of (5.7) for a function whose first derivative is only absolutely continuous. Absolute continuity is Mathlib's `AbsolutelyContinuousOnInterval` on every interval $[a,b]$.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 17, Section 5.1, (5.6)–(5.7)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Ergodicity_Operators

namespace JSQHalfinWhitt.Ergodicity

/-- Section 5.1, (5.6)–(5.7), p. 17: for `ℓ < u`, the smoothed indicator `φ = φ^{(ℓ,u)}` of (5.5) is
differentiable, `φ'` is absolutely continuous on every bounded interval, `φ'(ℓ) = φ'(u) = 0`,
`|φ'| ≤ 4/(u − ℓ)`, and at every point other than `ℓ`, `(u + ℓ)/2`, `u` the derivative `φ'` is
differentiable with `|φ''| ≤ 12/(u − ℓ)²`. -/
theorem eq_5_6_5_7 (l u : ℝ) (hlu : l < u) :
    Differentiable ℝ (smoothInd l u) ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval (deriv (smoothInd l u)) a b) ∧
      deriv (smoothInd l u) l = 0 ∧ deriv (smoothInd l u) u = 0 ∧
      (∀ x : ℝ, |deriv (smoothInd l u) x| ≤ 4 / (u - l)) ∧
      ∀ x : ℝ, x ≠ l → x ≠ (u + l) / 2 → x ≠ u →
        DifferentiableAt ℝ (deriv (smoothInd l u)) x ∧
          |deriv (deriv (smoothInd l u)) x| ≤ 12 / (u - l) ^ 2 := by sorry

end JSQHalfinWhitt.Ergodicity
