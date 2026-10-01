-- Prove2me | Theorems.Thm_HilbertSixteenth_finitely_many_limit_cycles
-- name    : HilbertSixteenth.finitely_many_limit_cycles
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T20:16:02.666703+00:00
-- url     : https://prove2.me/theorems/dc69bad9-d8c4-46ec-bc66-933ce2e1164b
-- title:
--   Finiteness of limit cycles of polynomial vector fields (Écalle, Ilyashenko)
-- statement:
--   Let $V=(P,Q)$ be any real polynomial vector field on $\mathbb R^2$. Then the set of limit cycles of
--   $$\dot x=P(x,y),\qquad \dot y=Q(x,y)$$
--   is finite.
--
--   This answers Problem 1 of the survey positively; it was claimed by Dulac in 1923 and proved independently by Écalle and Ilyashenko. It shows that the number of limit cycles of each individual system is a natural number, which is the starting point of the question of a uniform bound $H(d)$.
-- source:
--   J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015), no. 3, pp. 543–554, §2 (Problem 1): Dulac's claim, proved by Écalle (1992) and Ilyashenko (1991).

import Definitions.Def_HilbertSixteenth_PolyFields

namespace HilbertSixteenth
theorem finitely_many_limit_cycles (V : PolyField) :
    {O : Set (ℝ × ℝ) | IsLimitCycle V.toField O}.Finite := by sorry
end HilbertSixteenth
