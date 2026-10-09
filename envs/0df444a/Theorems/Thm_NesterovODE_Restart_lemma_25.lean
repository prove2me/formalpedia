-- Prove2me | Theorems.Thm_NesterovODE_Restart_lemma_25
-- name    : NesterovODE.Restart.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:49.297333+00:00
-- url     : https://prove2.me/theorems/a291f129-d3f4-4036-8c42-ef2440b89025
-- title:
--   Lemma 25, p. 41 — the speed restarting time satisfies T(x₀, f) ≥ 4/(5√L)
-- statement:
--   Let $0<\mu\le L$, $f\in\mathcal S_{\mu,L}$ with minimizer $x^\star$, let $x_0\ne x^\star$, and let $X$ solve (3) from $x_0$. Then the speed $\|\dot X\|$ strictly increases on $(0,4/(5\sqrt L))$:
--
--   $$\frac{\mathrm d\|\dot X(u)\|^2}{\mathrm du}>0\quad\text{for all }u\in\Bigl(0,\frac4{5\sqrt L}\Bigr),\qquad\text{hence}\qquad T(x_0,f)\ge\frac4{5\sqrt L}.$$
--
--   The lemma guarantees that each restart period of the speed restarting scheme lasts at least $4/(5\sqrt L)$, so restarts do not accumulate.
--
--   **Formalization Note** The statement is the membership of $4/(5\sqrt L)$ in the set $\{t>0:\forall u\in(0,t),\ \mathrm d\|\dot X(u)\|^2/\mathrm du>0\}$ whose supremum is $T$. This is what the proof establishes, and it implies $T\ge4/(5\sqrt L)$ whenever the set is bounded (Lemma 13). The derivative is written as $\langle\dot X(u),-\frac3u\dot X(u)-\nabla f(X(u))\rangle$, which is half of it. The hypothesis $x_0\ne x^\star$ is the convention of §5 (p. 22).
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 41, Lemma 25 (Appendix E); speed restarting time defined on p. 22

import Mathlib
import Definitions.Def_NesterovODE_Restart_Setting

namespace NesterovODE.Restart

open scoped RealInnerProductSpace

/-- Lemma 25 (p. 41): the speed restarting time satisfies `T(x₀, f) ≥ 4/(5√L)`, stated as
membership: `d‖Ẋ(u)‖²/du > 0` for every `u ∈ (0, 4/(5√L))`. Convention of §5: `x₀ ≠ x⋆`. -/
theorem lemma_25 (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (μ : ℝ) (L : NNReal)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hf : NesterovODE.StrongCvx.InSMuL μ L f)
    (x₀ xstar : NesterovODE.WellPosed.E n) (hmin : ∀ y, f xstar ≤ f y) (hx₀ : x₀ ≠ xstar)
    (X V : ℝ → NesterovODE.WellPosed.E n) (hX : NesterovODE.StrongCvx.IsSolution f 3 x₀ X V) :
    4 / (5 * Real.sqrt L) ∈ restartSet f X V := by sorry

end NesterovODE.Restart
