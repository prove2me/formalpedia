-- Prove2me | Theorems.Thm_HilbertSixteenth_generic_algebraic_limit_cycles_bound_attained
-- name    : HilbertSixteenth.generic_algebraic_limit_cycles_bound_attained
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:33:24.502404+00:00
-- url     : https://prove2.me/theorems/69d06e2b-c837-4f23-b2d4-5ae19742e5b1
-- title:
--   Theorem 4(b): the generic bounds are attained
-- statement:
--   For every $d\ge2$ there is a polynomial vector field $V$ of degree exactly $d$, all of whose irreducible invariant algebraic curves are generic, with exactly
--   $$\begin{cases} 1+\dfrac{(d-1)(d-2)}{2} & d \text{ even},\\[2mm] \dfrac{(d-1)(d-2)}{2} & d \text{ odd}\end{cases}$$
--   algebraic limit cycles.
--
--   Together with Theorem 4(a) this identifies the maximal number of algebraic limit cycles in the generic case; for even $d$ it gives the lower bound $H_a(d)\ge 1+\frac{(d-1)(d-2)}2$.
-- source:
--   J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015), no. 3, pp. 543–554, §7, Theorem 4, second sentence: 'Además estas cotas se alcanzan' (Llibre–Ramírez–Sadovskaia 2010).

import Definitions.Def_HilbertSixteenth_PolyFields

namespace HilbertSixteenth
theorem generic_algebraic_limit_cycles_bound_attained (d : ℕ) (hd : 2 ≤ d) :
    ∃ V : PolyField, V.degree = d ∧ HasGenericInvariantCurves V ∧
      numAlgebraicLimitCycles V = genericAlgebraicBound d := by sorry
end HilbertSixteenth
