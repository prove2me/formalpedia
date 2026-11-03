-- Prove2me | Theorems.Thm_Grothendieck_reducedIntegrand_eq_pi_inv_mul_integral
-- name    : Grothendieck.reducedIntegrand_eq_pi_inv_mul_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T01:56:23.868943+00:00
-- url     : https://prove2.me/theorems/03a496e6-a985-4c07-b162-2894219ac5c9
-- title:
--   The rounding integrand in Laplace form
-- statement:
--   Where both columns of the random matrix are nonzero,
--
--   $$
--   \mathrm{reducedIntegrand}_r(W)=\frac1\pi\,\langle X,Y\rangle\int_0^\infty\!\!\int_0^\infty (st)^{-1/2}e^{-(s\lVert X\rVert^2+t\lVert Y\rVert^2)}\,ds\,dt,
--   $$
--
--   with $X,Y$ the two columns of $W$.
--
--   This is the launch point of the whole substitution chain: it replaces the singular ratio $\langle X,Y\rangle/(\lVert X\rVert\lVert Y\rVert)$ by an inner product times a smooth two-parameter integral. The proof is the two published steps composed — the ratio form of the integrand and the Laplace identity $\frac1{\sqrt A\sqrt B}=\frac1\pi\iint(st)^{-1/2}e^{-(sA+tB)}$ applied with $A=\lVert X\rVert^2$, $B=\lVert Y\rVert^2$, using $\sqrt{\lVert X\rVert^2}=\lVert X\rVert$ — followed by nothing more than commutativity of multiplication.
--
--   The hypothesis is not cosmetic: at $\lVert X\rVert=0$ the left side is $0$ by Lean's convention $0^{-1}=0$ while the right side is generally not, so the identity holds only off that null set — which is enough, since the set where a Gaussian column vanishes has measure zero.
--
--   **Formalization Note** Supporting lemma for Lemma 2.1, not a verbatim statement of the paper.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Algorithm A (p. 82) and Lemma 2.1 (p. 84).

import Mathlib
import Definitions.Def_Grothendieck_Reduced

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The Laplace form of the rounding integrand.** Where both columns are nonzero,
`reducedIntegrand r W = π⁻¹ ⟨X,Y⟩ ∫₀^∞∫₀^∞ (st)^{-1/2} e^{-(s‖X‖²+t‖Y‖²)}`. -/
theorem reducedIntegrand_eq_pi_inv_mul_integral (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (hX : colFun r 0 W ≠ 0) (hY : colFun r 1 W ≠ 0) :
    reducedIntegrand r W
      = Real.pi⁻¹ * (inner ℝ (colFun r 0 W) (colFun r 1 W) *
          ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2))) := by sorry

end Grothendieck
