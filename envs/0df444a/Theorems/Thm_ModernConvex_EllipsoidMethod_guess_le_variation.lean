-- Prove2me | Theorems.Thm_ModernConvex_EllipsoidMethod_guess_le_variation
-- name    : ModernConvex.EllipsoidMethod.guess_le_variation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:04.018519+00:00
-- url     : https://prove2.me/theorems/172b54b1-4672-4ece-ab55-6050c69c9e2a
-- title:
--   Eq. (5.2.28) — the guesses satisfy L_t ≤ Var_R(f)
-- statement:
--   Let $n \ge 2$ and consider the convex program $\min\{f(x) : x \in X\}$ in $\mathbb R^n$ under assumption A: $f$ is convex on $\mathbb R^n$, $X$ is closed, bounded and convex with nonempty interior, $r, R > 0$, $X$ lies in the ball $E_0 = \{\|x\|_2 \le R\}$ and contains a Euclidean ball of radius $r$. Run the ellipsoid method with accuracy $\epsilon > 0$, a separation oracle for $X$ and a first order oracle for $f$. Let
--   $$\operatorname{Var}_R(f) = \max_{E_0} f - \min_{E_0} f.$$
--   If the method is still running after $t$ steps and step $t+1$ reaches rule 3, the guess $L_{t+1}$ it computes satisfies
--   $$L_{t+1} \le \operatorname{Var}_R(f).$$
--   (For $t = 0$ the initial guess is $L_0 = 0$.)
--
--   The guesses $L_t$ enter the termination test (5.2.17); this bound converts the test into the explicit step count of Theorem 5.2.1.
--
--   **Formalization Note** The maximum and minimum of $f$ on $E_0$ are given as reals `Vmax`, `Vmin` with `IsGreatest`/`IsLeast` of the image $f(E_0)$, so no supremum with a default value is involved; they exist because $f$ is continuous and $E_0$ compact. The hypotheses are those of Theorem 5.2.1, in whose proof (5.2.28) appears.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 352, Eq. (5.2.28) (proof of Theorem 5.2.1)

import Mathlib
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod

open Matrix MeasureTheory

namespace ModernConvex.EllipsoidMethod

/-- Ben-Tal–Nemirovski, p. 352, Eq. (5.2.28), in the proof of Theorem 5.2.1. In the setting of
Theorem 5.2.1, let `Var_R(f) = max_{E₀} f − min_{E₀} f` over the ball `E₀ = {‖x‖₂ ≤ R}`
(the maximum `Vmax` and minimum `Vmin` of `f` on `E₀`). Every guess `L_{t+1}` computed at a
step `t + 1` of the method (the method still running after `t` steps, step `t + 1` not stopping
by rule 2) satisfies `L_{t+1} ≤ Var_R(f)` (and `L₀ = 0`). -/
theorem guess_le_variation {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin)
    (t : ℕ) (s s' : State n) (hrun : run sep O R r ε t = Outcome.running s)
    (hstep : step sep O R s = StepResult.next s') :
    s'.L ≤ Vmax - Vmin := by sorry

end ModernConvex.EllipsoidMethod
