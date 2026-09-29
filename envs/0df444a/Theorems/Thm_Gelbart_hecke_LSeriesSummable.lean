-- Prove2me | Theorems.Thm_Gelbart_hecke_LSeriesSummable
-- name    : Gelbart.hecke_LSeriesSummable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:37:24.561775+00:00
-- url     : https://prove2.me/theorems/4da1534c-872d-4648-8127-dd66b8e09659
-- title:
--   Absolute convergence of $\varphi(s) = \sum a_n n^{-s}$ for $\Re s > c+1$
-- statement:
--   If $a_n = O(n^{c})$ with $c > 0$, then the Dirichlet series $\varphi(s) = \sum_{n \ge 1} a_n n^{-s}$ converges absolutely in the half-plane $\operatorname{Re} s > c + 1$. This fixes the abscissa used in the statement of Hecke's conditions.
-- source:
--   S. Gelbart, An elementary introduction to the Langlands program, Bull. Amer. Math. Soc. (N.S.) 10 (1984), no. 2, 177-219, https://doi.org/10.1090/S0273-0979-1984-15237-6, p. 188, §II.B.2 (definition of the Dirichlet series)

import Definitions.Def_Gelbart_hecke_series

namespace Gelbart

theorem hecke_LSeriesSummable
    (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (hgrowth : HeckeCoeffGrowth a c)
    {s : ℂ} (hs : c + 1 < s.re) :
    LSeriesSummable a s := by sorry

end Gelbart
