-- Prove2me | Theorems.Thm_ModernConvex_EllipsoidMethod_radius_decay
-- name    : ModernConvex.EllipsoidMethod.radius_decay
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:02.600993+00:00
-- url     : https://prove2.me/theorems/abf5dc56-c164-4d58-8b33-e7cc7bb273a4
-- title:
--   Eq. (5.2.21) — the radii ρ_τ of the ellipsoids satisfy ρ_τ ≤ exp{−τ/(2n²)}R
-- statement:
--   Let $n \ge 2$ and consider the convex program $\min\{f(x) : x \in X\}$ in $\mathbb R^n$ under assumption A: $f$ is convex on $\mathbb R^n$, $X$ is closed, bounded and convex with nonempty interior, $r, R > 0$, $X$ lies in the ball $E_0 = \{\|x\|_2 \le R\}$ and contains a Euclidean ball of radius $r$. Run the ellipsoid method with accuracy $\epsilon > 0$, a separation oracle for $X$ and a first order oracle for $f$ (definition `ModernConvex.EllipsoidMethod.EllipsoidMethod`).
--
--   If the method is still running after $t$ steps and step $\tau = t + 1$ reaches rule 3 (it does not stop because of a zero subgradient), the matrix $B_\tau$ it computes satisfies
--   $$\rho_\tau = |\operatorname{Det} B_\tau|^{1/n} \le \exp\{-\tau/(2n^2)\}\,R.$$
--
--   This is the volume decrease (5.2.14) accumulated over the run and expressed through the radius of the ball of the same volume as $E_\tau$; it drives the bound on the number of steps.
--
--   **Formalization Note** The book states (5.2.21) for $\tau = 1, \dots, t$ where $t$ is a step at which the method has not yet terminated or terminates by rule 4; in Lean this is every step $\tau = t + 1$ performed from a running state and ending with new data $(c_\tau, B_\tau, L_\tau)$, whether or not the termination test (5.2.17) then fires. The hypotheses are those of Theorem 5.2.1, in whose proof (5.2.21) appears.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 350, Eq. (5.2.21) (proof of Theorem 5.2.1)

import Mathlib
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod

open Matrix MeasureTheory

namespace ModernConvex.EllipsoidMethod

/-- Ben-Tal–Nemirovski, p. 350, Eq. (5.2.21), in the proof of Theorem 5.2.1. Let the ellipsoid
method with accuracy `ε > 0` be applied to (5.2.9) of dimension `n ≥ 2` under assumption A,
with a separation oracle for `X` and a first order oracle for `f`. If the method is still
running after `t` steps and step `t + 1` performs rule 3 (it does not stop by rule 2), the
new ellipsoid `E_{t+1} = {c_{t+1} + B_{t+1}u | uᵀu ≤ 1}` satisfies
`ρ_{t+1} = |Det B_{t+1}|^{1/n} ≤ exp{−(t+1)/(2n²)} R`. -/
theorem radius_decay {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (s s' : State n) (hrun : run sep O R r ε t = Outcome.running s)
    (hstep : step sep O R s = StepResult.next s') :
    radius s'.B ≤ Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) * R := by sorry

end ModernConvex.EllipsoidMethod
