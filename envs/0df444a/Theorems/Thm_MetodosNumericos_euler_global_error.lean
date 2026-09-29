-- Prove2me | Theorems.Thm_MetodosNumericos_euler_global_error
-- name    : MetodosNumericos.euler_global_error
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:00:36.692419+00:00
-- url     : https://prove2.me/theorems/b762b177-6cba-4906-a633-74ccb0214b33
-- title:
--   Global error of Euler's method is $O(h)$
-- statement:
--   Let $\\varphi$ solve $y' = f(x,y)$, $y(x_0)=y_0$ on $[x_0,X]$, be twice continuously differentiable there, and let $f$ be Lipschitz in $y$ with constant $L$ for $x \\in [x_0,X]$. Then there is $C>0$ such that for every step $h \\in (0,1]$ and every index $i$ with $x_0+ih \\le X$, the Euler iterate satisfies $|y_i - \\varphi(x_0+ih)| \\le C h$. This is the source's statement that the global error of Euler's method is $E = O(h)$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 9, §9.7 (erro local e global) and §9.9, pp. 191–192.

import Mathlib
import Definitions.Def_MetodosNumericos_edoDefs

namespace MetodosNumericos

theorem euler_global_error (f : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (x0 y0 X L : ℝ) (hX : x0 < X)
    (hphi0 : phi x0 = y0)
    (hsol : ∀ x ∈ Set.Icc x0 X, HasDerivAt phi (f x (phi x)) x)
    (hphi2 : ContDiffOn ℝ 2 phi (Set.Icc x0 X))
    (hlip : ∀ x ∈ Set.Icc x0 X, ∀ u v : ℝ, |f x u - f x v| ≤ L * |u - v|) :
    ∃ C > 0, ∀ h ∈ Set.Ioc (0 : ℝ) 1, ∀ i : ℕ, x0 + i * h ≤ X →
      |eulerSeq f x0 y0 h i - phi (x0 + i * h)| ≤ C * h := by sorry

end MetodosNumericos
