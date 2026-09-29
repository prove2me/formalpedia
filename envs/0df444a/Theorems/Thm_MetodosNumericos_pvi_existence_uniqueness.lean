-- Prove2me | Theorems.Thm_MetodosNumericos_pvi_existence_uniqueness
-- name    : MetodosNumericos.pvi_existence_uniqueness
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:46:17.239239+00:00
-- url     : https://prove2.me/theorems/946ff125-e7e7-42b9-905b-f7bf3bdcc702
-- title:
--   Local existence and uniqueness for the initial value problem
-- statement:
--   If $f$ is continuous on a rectangle around $(x_0,y_0)$ and Lipschitz in $y$ there, then for some $h>0$ the problem $y'=f(x,y)$, $y(x_0)=y_0$ has a solution on $[x_0-h,x_0+h]$ taking values in the rectangle, and any two such solutions agree on that interval. This is Teorema 9.4.1, with the bounded partial derivative replaced by an explicit Lipschitz condition.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 9, Teorema 9.4.1, p. 185.

import Mathlib

namespace MetodosNumericos

theorem pvi_existence_uniqueness (f : ℝ → ℝ → ℝ) (x0 y0 a b L : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Icc (x0 - a) (x0 + a) ×ˢ Set.Icc (y0 - b) (y0 + b)))
    (hlip : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ u ∈ Set.Icc (y0 - b) (y0 + b),
      ∀ v ∈ Set.Icc (y0 - b) (y0 + b), |f x u - f x v| ≤ L * |u - v|) :
    ∃ h > 0,
      (∃ phi : ℝ → ℝ, phi x0 = y0 ∧
        (∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt phi (f x (phi x)) x) ∧
        ∀ x ∈ Set.Icc (x0 - h) (x0 + h), phi x ∈ Set.Icc (y0 - b) (y0 + b)) ∧
      (∀ phi psi : ℝ → ℝ,
        (phi x0 = y0 ∧ ∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt phi (f x (phi x)) x) →
        (psi x0 = y0 ∧ ∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt psi (f x (psi x)) x) →
        (∀ x ∈ Set.Icc (x0 - h) (x0 + h), phi x ∈ Set.Icc (y0 - b) (y0 + b)) →
        (∀ x ∈ Set.Icc (x0 - h) (x0 + h), psi x ∈ Set.Icc (y0 - b) (y0 + b)) →
        Set.EqOn phi psi (Set.Icc (x0 - h) (x0 + h))) := by sorry

end MetodosNumericos
