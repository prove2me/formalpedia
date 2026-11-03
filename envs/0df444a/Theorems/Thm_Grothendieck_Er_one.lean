-- Prove2me | Theorems.Thm_Grothendieck_Er_one
-- name    : Grothendieck.Er_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:22:24.306108+00:00
-- url     : https://prove2.me/theorems/521c0aeb-051c-4bc1-b113-50aa87780fac
-- title:
--   The endpoint $E_r(1)=1$
-- statement:
--   For every integer $r\ge1$ the series of the paper attains the value $1$ at $t=1$:
--
--   $$
--   E_r(1)=\sum_{k\ge0} C_r\frac{(1/2)_k(1/2)_k}{(r/2+1)_k\,k!}=1 .
--   $$
--
--   The paper uses exactly this identity in the proof of Proposition 3.3, where it writes $E_r(1)=\sum_k a_k=1$ to compare $E_r$ with the linear function $C_rz$ on the boundary circle. Combined with the oddness of $E_r$ (immediate from the series) it gives $E_r(-1)=-1$, i.e. the case $u=\pm v$, $|u\cdot v|=1$, of the matrix Grothendieck identity — the case that no Laplace-transform or Fubini route to that identity reaches.
--
--   The proof takes $t\to1^-$ in the Beta-integral representation of $E_r$ (`Grothendieck.Er_eq_betaIntegral`), using dominated convergence and the Beta integral $\int_0^1u^{-1/2}(1-u)^{r/2-1}du=\sqrt\pi\,\Gamma(r/2)/\Gamma((r+1)/2)$, whose constant cancels $C_r$ exactly; no Gauss summation theorem is needed.
--
--   **Formalization Note** The statement is `Er r 1 = 1` for the paper's series `Er`, proved from the mission's definition layer alone.
-- source:
--   Briet-de Oliveira Filho-Vallentin, Theory of Computing 10(4), 2014, Proposition 3.3, p. 88.

import Mathlib
import Definitions.Def_Grothendieck_Series

open scoped BigOperators Real

namespace Grothendieck

theorem Er_one (r : ℕ) (hr : 1 ≤ r) : Er r 1 = 1 := by sorry

end Grothendieck
