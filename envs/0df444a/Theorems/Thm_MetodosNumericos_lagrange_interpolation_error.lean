-- Prove2me | Theorems.Thm_MetodosNumericos_lagrange_interpolation_error
-- name    : MetodosNumericos.lagrange_interpolation_error
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:00:43.842258+00:00
-- url     : https://prove2.me/theorems/da0931eb-ee0f-4da0-9456-2a0c184db508
-- title:
--   Lagrange interpolation error formula
-- statement:
--   Let $x_0 < \\dots < x_n$ lie in $(a,b)$ and let $f$ be $n+1$ times continuously differentiable on $(a,b)$. Then for every $x \\in (a,b)$ different from all nodes there is $\\xi \\in (a,b)$ with $$f(x) = P_n(x) + \\left(\\prod_{k=0}^{n}(x-x_k)\\right)\\frac{f^{(n+1)}(\\xi)}{(n+1)!},$$ where $P_n$ is the Lagrange interpolating polynomial of $f$ at the nodes. This is Proposição 7.3.1.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 7, Proposição 7.3.1, pp. 140–141.

import Mathlib
import Definitions.Def_MetodosNumericos_interpolacaoDefs

namespace MetodosNumericos

theorem lagrange_interpolation_error {n : ℕ} (f : ℝ → ℝ) (a b : ℝ) (xs : Fin (n + 1) → ℝ)
    (hxs : StrictMono xs) (hmem : ∀ i, xs i ∈ Set.Ioo a b)
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (Set.Ioo a b))
    (x : ℝ) (hx : x ∈ Set.Ioo a b) (hne : ∀ i, x ≠ xs i) :
    ∃ xi ∈ Set.Ioo a b,
      f x = lagrangeInterp xs (fun i => f (xs i)) x +
        (∏ k : Fin (n + 1), (x - xs k)) *
          (iteratedDerivWithin (n + 1) f (Set.Ioo a b) xi / (Nat.factorial (n + 1) : ℝ)) := by
  sorry

end MetodosNumericos
