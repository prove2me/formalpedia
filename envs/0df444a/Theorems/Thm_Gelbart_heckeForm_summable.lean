-- Prove2me | Theorems.Thm_Gelbart_heckeForm_summable
-- name    : Gelbart.heckeForm_summable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:36:56.728121+00:00
-- url     : https://prove2.me/theorems/c6e3ff25-7c55-460e-8cde-f07e326cc308
-- title:
--   Convergence of $\sum a_n e^{2\pi i n z/h}$ on the upper half-plane
-- statement:
--   If $a_n = O(n^{c})$ for some $c > 0$ and $h > 0$, then for every $z$ with $\operatorname{Im} z > 0$ the family $\left(a_n e^{2\pi i n z/h}\right)_{n \ge 0}$ is summable. This is the assertion, implicit in Gelbart's "the function defined in $H$" (p. 188), that $f$ is well defined on the upper half-plane: the exponential decays geometrically in $n$ and dominates the polynomial growth of the coefficients.
-- source:
--   S. Gelbart, An elementary introduction to the Langlands program, Bull. Amer. Math. Soc. (N.S.) 10 (1984), no. 2, 177-219, https://doi.org/10.1090/S0273-0979-1984-15237-6, p. 188, §II.B.2 (definition of f)

import Definitions.Def_Gelbart_hecke_series

namespace Gelbart

theorem heckeForm_summable
    (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * z / h) := by sorry

end Gelbart
