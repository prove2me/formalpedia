-- Prove2me | Theorems.Thm_MetodosNumericos_picard_error_bound
-- name    : MetodosNumericos.picard_error_bound
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-20T16:48:33.772986+00:00
-- url     : https://prove2.me/theorems/5036de89-bc94-4d7e-b979-6869f7682ccf
-- title:
--   Picard error bound $|\\varphi - y_k| \\le M N^{k-1}h^k/k!$
-- statement:
--   With $M$ a bound for $|f|$ and $N$ a Lipschitz constant in $y$ on the rectangle, and $h = \\min\\{a, b/M\\}$, the $k$-th Picard iterate satisfies $|\\varphi(x) - y_k(x)| \\le \\frac{M N^{k-1}}{k!}h^k$ for every $x \\in [x_0-h,x_0+h]$ and every $k \\ge 1$, where $\\varphi$ is a solution of the initial value problem. This is the estimate stated in §9.5.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 9, §9.5 Método de Picard, p. 186.

import Mathlib
import Definitions.Def_MetodosNumericos_edoDefs

namespace MetodosNumericos

theorem picard_error_bound (f : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (x0 y0 a b M N h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) (hN : 0 ≤ N) (hh : h = min a (b / M))
    (hbound : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ y ∈ Set.Icc (y0 - b) (y0 + b), |f x y| ≤ M)
    (hlip : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ u ∈ Set.Icc (y0 - b) (y0 + b),
      ∀ v ∈ Set.Icc (y0 - b) (y0 + b), |f x u - f x v| ≤ N * |u - v|)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Icc (x0 - a) (x0 + a) ×ˢ Set.Icc (y0 - b) (y0 + b)))
    (hphi0 : phi x0 = y0)
    (hsol : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt phi (f x (phi x)) x)
    (hrange : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), phi x ∈ Set.Icc (y0 - b) (y0 + b))
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : x ∈ Set.Icc (x0 - h) (x0 + h)) :
    |phi x - picardSeq f x0 y0 k x| ≤ M * N ^ (k - 1) * h ^ k / (Nat.factorial k : ℝ) := by
  sorry

end MetodosNumericos
