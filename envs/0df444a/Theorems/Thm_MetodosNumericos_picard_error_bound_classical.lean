-- Prove2me | Theorems.Thm_MetodosNumericos_picard_error_bound_classical
-- name    : MetodosNumericos.picard_error_bound_classical
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-24T14:14:54.15102+00:00
-- url     : https://prove2.me/theorems/9f69c9ce-7ddc-4936-8bcb-e7d8702ed7b6
-- title:
--   §9.5 — error of the k-th Picard iterate (classical bound)
-- statement:
--   With $M$ a bound for $|f|$ and $N$ a Lipschitz constant in $y$ on the rectangle, and $h = \min\{a, b/M\}$, the $k$-th Picard iterate satisfies $$|\varphi(x) - y_k(x)| \le \frac{M N^{k}}{(k+1)!}\,h^{k+1}$$ for every $x \in [x_0-h,x_0+h]$ and every $k \ge 0$, where $\varphi$ is a solution of the initial value problem with values in the rectangle and $y_0 \equiv y_0$, $y_{k+1}(x) = y_0 + \int_{x_0}^{x} f(t, y_k(t))\,dt$ are the Picard iterates of §9.5.
--
--   **Correction (moderator).** The bound printed on p. 186 of the source, $|\varphi(x)-y_k(x)| \le M N^{k-1} h^k / k!$, is off by one level of the iteration: it is the classical estimate for $y_{k-1}$, not for $y_k$, and it fails for $k = 1$ (the milestone stating it is recorded as disproved). This statement carries the classical estimate, obtained by induction from $|\varphi(x) - y_0| \le M|x - x_0|$ and the Lipschitz condition, with all iterates staying in the rectangle because $Mh \le b$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 9, §9.5 Método de Picard, p. 186.

import Mathlib
import Definitions.Def_MetodosNumericos_edoDefs

namespace MetodosNumericos

theorem picard_error_bound_classical (f : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (x0 y0 a b M N h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) (hN : 0 ≤ N) (hh : h = min a (b / M))
    (hbound : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ y ∈ Set.Icc (y0 - b) (y0 + b), |f x y| ≤ M)
    (hlip : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ u ∈ Set.Icc (y0 - b) (y0 + b),
      ∀ v ∈ Set.Icc (y0 - b) (y0 + b), |f x u - f x v| ≤ N * |u - v|)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Icc (x0 - a) (x0 + a) ×ˢ Set.Icc (y0 - b) (y0 + b)))
    (hphi0 : phi x0 = y0)
    (hsol : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt phi (f x (phi x)) x)
    (hrange : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), phi x ∈ Set.Icc (y0 - b) (y0 + b))
    (k : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (x0 - h) (x0 + h)) :
    |phi x - picardSeq f x0 y0 k x| ≤ M * N ^ k * h ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
  sorry

end MetodosNumericos
