-- Prove2me | Theorems.Thm_Grothendieck_laplace_integral_mul_norm_eq_pi
-- name    : Grothendieck.laplace_integral_mul_norm_eq_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T02:18:17.091181+00:00
-- url     : https://prove2.me/theorems/b5a2ec09-3974-4f8f-be44-fbef56cb7581
-- title:
--   The Fubini majorant has total mass $\pi$
-- statement:
--   For nonzero columns $X,Y$ of an $r\times2$ matrix,
--
--   $$
--   \lVert X\rVert\lVert Y\rVert\int_0^\infty\!\!\int_0^\infty (st)^{-1/2}e^{-(s\lVert X\rVert^2+t\lVert Y\rVert^2)}\,ds\,dt=\pi .
--   $$
--
--   This is the total mass of the dominating function in the Fubini step of Lemma 2.1. The Laplace identity gives $\frac{1}{\sqrt A\sqrt B}=\frac1\pi\iint(st)^{-1/2}e^{-(sA+tB)}$; at $A=\lVert X\rVert^2$, $B=\lVert Y\rVert^2$ with $\sqrt{\lVert X\rVert^2}=\lVert X\rVert$ this reads $\frac{1}{\lVert X\rVert\lVert Y\rVert}=\frac1\pi\iint(st)^{-1/2}e^{-\ldots}$, and multiplying by $\lVert X\rVert\lVert Y\rVert$ gives $\pi$.
--
--   Why it is the right normalisation: bounding $\lvert\langle X,Y\rangle\rvert\le\lVert X\rVert\lVert Y\rVert$ turns the signed integrand of the Fubini step into a multiple of this one, and integrating the bound over $W$ against the probability law gives at most $\pi$ — no growth condition, no moment computation, no ad-hoc estimate. It is the reason the swap needs no integrability hypothesis beyond Tonelli.
--
--   **Formalization Note** Supporting lemma for Lemma 2.1, not a verbatim statement of the paper.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Algorithm A (p. 82) and Lemma 2.1 (p. 84).

import Mathlib
import Definitions.Def_Grothendieck_Reduced

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The Fubini majorant has total mass `π`.** For nonzero columns `X`, `Y`,
`‖X‖‖Y‖ ∫₀^∞∫₀^∞ (st)^{-1/2} e^{-(s‖X‖²+t‖Y‖²)} = π`. -/
theorem laplace_integral_mul_norm_eq_pi {r : ℕ} (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (hX : colFun r 0 W ≠ 0) (hY : colFun r 1 W ≠ 0) :
    (‖colFun r 0 W‖ * ‖colFun r 1 W‖) *
        (∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
          (s * t) ^ (-(1/2) : ℝ) *
            Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2)))
      = Real.pi := by sorry

end Grothendieck
