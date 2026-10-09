-- Prove2me | Theorems.Thm_NesterovODE_Restart_eq_30
-- name    : NesterovODE.Restart.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:39:11.209544+00:00
-- url     : https://prove2.me/theorems/d7ce1134-5a4f-4ebc-b380-78b7b2ca8d35
-- title:
--   (30), p. 23 — for 0 < t < √(12/L), ‖Ẋ(t)‖ lies within L‖∇f(x₀)‖t³/(48(1 − Lt²/12)) of (t/4)‖∇f(x₀)‖
-- statement:
--   Let $0<\mu\le L$, $f\in\mathcal S_{\mu,L}$, and let $X$ solve (3) from $x_0$ with $\dot X(0)=0$. For $0<t<\sqrt{12/L}$,
--
--   $$\Bigl\|\dot X(t)+\frac t4\nabla f(x_0)\Bigr\|\le\frac{L\|\nabla f(x_0)\|t^3}{48(1-Lt^2/12)},$$
--
--   and consequently
--
--   $$\frac t4\|\nabla f(x_0)\|-\frac{L\|\nabla f(x_0)\|t^3}{48(1-Lt^2/12)}\le\|\dot X(t)\|\le\frac t4\|\nabla f(x_0)\|+\frac{L\|\nabla f(x_0)\|t^3}{48(1-Lt^2/12)}.$$
--
--   Moreover the lower bound is nonnegative for $0<t\le\sqrt{6/L}$, in particular on the interval $0<t<4/(5\sqrt L)$ where it is used.
--
--   For small times the velocity is close to $-\tfrac t4\nabla f(x_0)$, the velocity of the ODE with frozen gradient. The two-sided bound is used in the proofs of Lemma 12 and Lemma 13.
--
--   **Formalization Note** The page writes the leftmost "$0\le$" of (30) for all $t<\sqrt{12/L}$; it holds exactly when $t\le\sqrt{6/L}$, so it is stated on that range, which contains $(0,4/(5\sqrt L))$. The middle equality $\|\dot X(t)+\frac t4\nabla f(x_0)\|=\frac1{t^3}\|I(t)\|$ of the display before (30) is not stated, since $I(t)$ is not a mission definition. Standing assumption $f\in\mathcal S_{\mu,L}$ (only $\mathcal F_L$ is used).
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 23, proof of Lemma 12, display before (30) and (30)

import Mathlib
import Definitions.Def_NesterovODE_Restart_Setting

namespace NesterovODE.Restart

open scoped RealInnerProductSpace

/-- Display (30) and the display before it (p. 23, proof of Lemma 12): for `0 < t < √(12/L)`,
`‖Ẋ(t) + (t/4)∇f(x₀)‖ ≤ L‖∇f(x₀)‖t³/(48(1 − Lt²/12))`, hence the two-sided bound on `‖Ẋ(t)‖`;
the leftmost `0 ≤` of (30) holds exactly for `0 < t ≤ √(6/L)`. -/
theorem eq_30 (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (μ : ℝ) (L : NNReal)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hf : NesterovODE.StrongCvx.InSMuL μ L f)
    (x₀ : NesterovODE.WellPosed.E n) (X V : ℝ → NesterovODE.WellPosed.E n) (hX : NesterovODE.StrongCvx.IsSolution f 3 x₀ X V) :
    (∀ t : ℝ, 0 < t → t < Real.sqrt (12 / L) →
      ‖V t + (t / 4) • gradient f x₀‖ ≤
          L * ‖gradient f x₀‖ * t ^ 3 / (48 * (1 - L * t ^ 2 / 12)) ∧
      t / 4 * ‖gradient f x₀‖ - L * ‖gradient f x₀‖ * t ^ 3 / (48 * (1 - L * t ^ 2 / 12))
          ≤ ‖V t‖ ∧
      ‖V t‖ ≤
          t / 4 * ‖gradient f x₀‖ + L * ‖gradient f x₀‖ * t ^ 3 / (48 * (1 - L * t ^ 2 / 12))) ∧
    (∀ t : ℝ, 0 < t → t ≤ Real.sqrt (6 / L) →
      0 ≤ t / 4 * ‖gradient f x₀‖ - L * ‖gradient f x₀‖ * t ^ 3 / (48 * (1 - L * t ^ 2 / 12)))
    := by sorry

end NesterovODE.Restart
