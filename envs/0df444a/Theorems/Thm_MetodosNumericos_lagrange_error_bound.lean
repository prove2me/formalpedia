-- Prove2me | Theorems.Thm_MetodosNumericos_lagrange_error_bound
-- name    : MetodosNumericos.lagrange_error_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:54:49.684629+00:00
-- url     : https://prove2.me/theorems/85ba22df-97da-4333-b288-3022f662123e
-- title:
--   Error bound for polynomial interpolation
-- statement:
--   Under the hypotheses of the goal theorem, if in addition $|f^{(n+1)}(y)| \\le M$ for every $y \\in (a,b)$, then $$|f(x) - P_n(x)| \\le \\frac{M}{(n+1)!}\\prod_{k=0}^{n}|x - x_k|.$$ This is Proposição 7.3.2.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 7, Proposição 7.3.2, pp. 141–142.

import Mathlib
import Definitions.Def_MetodosNumericos_interpolacaoDefs

namespace MetodosNumericos

theorem lagrange_error_bound {n : ℕ} (f : ℝ → ℝ) (a b M : ℝ) (xs : Fin (n + 1) → ℝ)
    (hxs : StrictMono xs) (hmem : ∀ i, xs i ∈ Set.Ioo a b)
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (Set.Ioo a b))
    (hM : ∀ y ∈ Set.Ioo a b, |iteratedDerivWithin (n + 1) f (Set.Ioo a b) y| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Ioo a b) (hne : ∀ i, x ≠ xs i) :
    |f x - lagrangeInterp xs (fun i => f (xs i)) x| ≤
      M / (Nat.factorial (n + 1) : ℝ) * ∏ k : Fin (n + 1), |x - xs k| := by sorry

end MetodosNumericos
