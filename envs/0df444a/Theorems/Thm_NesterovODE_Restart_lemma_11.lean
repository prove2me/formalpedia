-- Prove2me | Theorems.Thm_NesterovODE_Restart_lemma_11
-- name    : NesterovODE.Restart.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:06.364531+00:00
-- url     : https://prove2.me/theorems/fcf4a43d-4e1b-422a-a042-208a339a52ea
-- title:
--   Lemma 11, p. 23 — for t < √(12/L), M(t) = sup_{u∈(0,t]} ‖Ẋ(u)‖/u ≤ ‖∇f(x₀)‖/(4(1 − Lt²/12))
-- statement:
--   Let $0<\mu\le L$ and $f\in\mathcal S_{\mu,L}$ on $\mathbb R^n$, and let $X$ solve the ODE (3), $\ddot X+\frac3t\dot X+\nabla f(X)=0$, with $X(0)=x_0$, $\dot X(0)=0$. Write $M(t)=\sup_{u\in(0,t]}\|\dot X(u)\|/u$. For every $t<\sqrt{12/L}$,
--
--   $$M(t)\le\frac{\|\nabla f(x_0)\|}{4\,(1-Lt^2/12)}.$$
--
--   The lemma controls the velocity of the unrestarted trajectory on a short initial interval. It is the basic estimate behind (30), Lemma 25 and Lemma 12.
--
--   **Formalization Note** The supremum is stated pointwise: $\|\dot X(u)\|/u\le\|\nabla f(x_0)\|/(4(1-Lt^2/12))$ for every $u\in(0,t]$, which is equivalent to the bound on $M(t)$ and has no junk value. The hypothesis $f\in\mathcal S_{\mu,L}$ is the standing assumption of §5 (p. 21); the proof uses only $f\in\mathcal F_L$. Every solution of (3) is covered.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 23, Lemma 11 (M(t) defined on p. 23; proof in Appendix E, p. 40)

import Mathlib
import Definitions.Def_NesterovODE_Restart_Setting

namespace NesterovODE.Restart

open scoped RealInnerProductSpace

/-- Lemma 11 (p. 23): for `t < √(12/L)`, `M(t) = sup_{u ∈ (0,t]} ‖Ẋ(u)‖/u` is at most
`‖∇f(x₀)‖ / (4(1 − Lt²/12))`, stated as a bound on every `‖Ẋ(u)‖/u`, `u ∈ (0, t]`. -/
theorem lemma_11 (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (μ : ℝ) (L : NNReal)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hf : NesterovODE.StrongCvx.InSMuL μ L f)
    (x₀ : NesterovODE.WellPosed.E n) (X V : ℝ → NesterovODE.WellPosed.E n) (hX : NesterovODE.StrongCvx.IsSolution f 3 x₀ X V) :
    ∀ t : ℝ, t < Real.sqrt (12 / L) → ∀ u ∈ Set.Ioc 0 t,
      ‖V u‖ / u ≤ ‖gradient f x₀‖ / (4 * (1 - L * t ^ 2 / 12)) := by sorry

end NesterovODE.Restart
