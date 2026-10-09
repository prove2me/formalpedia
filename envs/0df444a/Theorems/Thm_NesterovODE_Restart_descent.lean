-- Prove2me | Theorems.Thm_NesterovODE_Restart_descent
-- name    : NesterovODE.Restart.descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:00.075527+00:00
-- url     : https://prove2.me/theorems/944b911c-0a49-47c2-bf02-b29b2f4a2ace
-- title:
--   p. 22, §5.1 — df(X(t))/dt = ⟨∇f(X), Ẋ⟩ = −(3/t)‖Ẋ‖² − ½ d‖Ẋ‖²/dt ≤ 0 for t ≤ T
-- statement:
--   Let $0<\mu\le L$, $f\in\mathcal S_{\mu,L}$, and let $X$ solve (3) from $x_0$. For every $t>0$ the function $t\mapsto f(X(t))$ is differentiable, and
--
--   $$\frac{\mathrm d f(X(t))}{\mathrm dt}=\langle\nabla f(X),\dot X\rangle=-\frac3t\|\dot X\|^2-\frac12\frac{\mathrm d\|\dot X\|^2}{\mathrm dt}.$$
--
--   Before the speed restarting time this derivative is nonpositive: for every $t$ with $0<t\le T$ (that is, every $t$ in the set whose supremum is $T$), $\frac{\mathrm d f(X(u))}{\mathrm du}\le0$ for $u\in(0,t]$, and $f(X(\cdot))$ is nonincreasing on $[0,t]$.
--
--   This is why the restarted scheme never increases the objective: between two restarts it follows (3) while the speed increases.
--
--   **Formalization Note** $\frac12\mathrm d\|\dot X\|^2/\mathrm dt$ is written as $\langle\dot X(t),-\frac3t\dot X(t)-\nabla f(X(t))\rangle$. "For $t\le T$" is expressed by $t\in\{t>0:\forall u\in(0,t),\ \mathrm d\|\dot X(u)\|^2/\mathrm du>0\}$, which is the interval $(0,T]$ when $T$ is finite and avoids the junk value of `sSup`. Standing assumption $f\in\mathcal S_{\mu,L}$ (only $C^1$ is used).
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 22, §5.1, display after the definition of the speed restarting time

import Mathlib
import Definitions.Def_NesterovODE_Restart_Setting

namespace NesterovODE.Restart

open scoped RealInnerProductSpace

/-- The descent display (p. 22): for `t > 0`, `d f(X(t))/dt = ⟨∇f(X), Ẋ⟩ = −(3/t)‖Ẋ‖² −
(1/2) d‖Ẋ‖²/dt`; and before the speed restarting time (`t ∈ restartSet`, i.e. `0 < t ≤ T`) this
derivative is `≤ 0` on `(0, t]` and `f ∘ X` is nonincreasing on `[0, t]`. -/
theorem descent (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (μ : ℝ) (L : NNReal)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hf : NesterovODE.StrongCvx.InSMuL μ L f)
    (x₀ : NesterovODE.WellPosed.E n) (X V : ℝ → NesterovODE.WellPosed.E n) (hX : NesterovODE.StrongCvx.IsSolution f 3 x₀ X V) :
    (∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => f (X s)) ⟪gradient f (X t), V t⟫ t ∧
      ⟪gradient f (X t), V t⟫ = -(3 / t) * ‖V t‖ ^ 2 - halfSpeedDeriv f X V t) ∧
    (∀ t ∈ restartSet f X V,
      (∀ u ∈ Set.Ioc 0 t, ⟪gradient f (X u), V u⟫ ≤ 0) ∧
      AntitoneOn (fun s => f (X s)) (Set.Icc 0 t)) := by sorry

end NesterovODE.Restart
