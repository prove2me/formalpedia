-- Prove2me | Theorems.Thm_HunterPDE_Semilinear_local_existence
-- name    : HunterPDE.Semilinear.local_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:15:32.037923+00:00
-- url     : https://prove2.me/theorems/0ade23cc-fd27-4ab7-a062-16bc65c2369f
-- title:
--   Theorem 5.49 — local existence and uniqueness of mild H^{2α} solutions of u_t = Δu + λu − γu^m, 1 ≤ n ≤ 3
-- statement:
--   Consider the semilinear heat equation on $\mathbb{R}^n$,
--   $$u_t = \Delta u + \lambda u - \gamma u^m, \qquad u(x,0) = g(x),$$
--   with $\lambda, \gamma \in \mathbb{R}$ and $m \ge 1$. Suppose that $1 \le n \le 3$ and $n/4 < \alpha < 1$. Then there exists $T > 0$, depending only on $\alpha$, $n$, $\|g\|_{H^{2\alpha}}$ and the coefficients $\lambda, \gamma, m$, such that the problem has a unique mild solution $u \in C([0,T]; H^{2\alpha}(\mathbb{R}^n))$, i.e. a unique $u \in C([0,T];H^{2\alpha})$ with
--   $$u(t) = e^{-tA}g + \int_0^t e^{-(t-s)A}\big(\lambda u(s) - \gamma u(s)^m\big)\, ds \qquad (0 \le t \le T).$$
--
--   This is the model local well-posedness result for semilinear parabolic equations: the heat semigroup's smoothing compensates for the nonlinearity, and a contraction argument in $C([0,T];H^{2\alpha})$ gives a solution on a time interval controlled by the size of the data.
--
--   **Formalization Note.** "Depending only on $\|g\|_{H^{2\alpha}}$" is formalized as: for every $R > 0$ there is a single $T > 0$ that works for every $g$ with $\|g\|_{H^{2\alpha}} \le R$. Both existence and uniqueness are stated; uniqueness is among all mild solutions on $[0,T]$, up to equality almost everywhere in $x$ at each time. Functions are real-valued, $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`, and $m \ge 1$ (for $m = 0$ the reaction term $-\gamma$ is not in $L^2$).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 154, Theorem 5.49

import Mathlib
import Definitions.Def_HunterPDE_Semilinear_SobolevHs
import Definitions.Def_HunterPDE_Semilinear_HeatSemigroup
import Definitions.Def_HunterPDE_Semilinear_MildSolution

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Semilinear

/-- Theorem 5.49 of Hunter, *Notes on PDEs* (p. 154): suppose that `1 ≤ n ≤ 3` and
`n/4 < α < 1`. Then there exists `T > 0`, depending only on `α`, `n`, `‖g‖_{H^{2α}}` and the
coefficients of `f(u) = λu − γu^m`, such that (5.34), `u_t = Δu + λu − γu^m`, `u(x,0) = g(x)`,
has a unique mild solution `u ∈ C([0,T]; H^{2α})` in the sense of Definition 5.48.

"Depending only on `‖g‖_{H^{2α}}`" is read as: for every `R > 0` there is one `T > 0` (chosen
after `n, α, λ, γ, m, R`) that works for every `g` with `‖g‖_{H^{2α}} ≤ R`. Existence and
uniqueness are both stated; uniqueness is among all mild solutions on `[0,T]`, i.e. in
`C([0,T]; H^{2α})`, up to equality almost everywhere in `x` at each time. `m ≥ 1`. -/
theorem local_existence (n : ℕ) (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (α : ℝ) (hα : (n : ℝ) / 4 < α)
    (hα1 : α < 1) (lam gam : ℝ) (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (hR : 0 < R) :
    ∃ T : ℝ, 0 < T ∧ ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      hsNormReal n (2 * α) g ≤ ENNReal.ofReal R →
        (∃ u : ℝ → EuclideanSpace ℝ (Fin n) → ℝ, IsMildSolution n α lam gam m g T u) ∧
        (∀ u v : ℝ → EuclideanSpace ℝ (Fin n) → ℝ,
          IsMildSolution n α lam gam m g T u → IsMildSolution n α lam gam m g T v →
          ∀ t ∈ Set.Icc (0 : ℝ) T, u t =ᵐ[volume] v t) := by sorry

end HunterPDE.Semilinear
