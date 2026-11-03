-- Prove2me | Theorems.Thm_Grothendieck_reducedIntegrand_eq_pi_inv_mul_integral_all
-- name    : Grothendieck.reducedIntegrand_eq_pi_inv_mul_integral_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T02:13:43.627812+00:00
-- url     : https://prove2.me/theorems/cae1a3b4-0672-4710-9d37-e6b7be2e7c34
-- title:
--   The rounding integrand in Laplace form, with no side conditions
-- statement:
--   For every $r$ and every $r\times 2$ matrix $W$, with $X,Y$ its columns,
--
--   $$
--   \mathrm{reducedIntegrand}_r(W)=\frac1\pi\,\langle X,Y\rangle\int_0^\infty\!\!\int_0^\infty (st)^{-1/2}e^{-(s\lVert X\rVert^2+t\lVert Y\rVert^2)}\,ds\,dt ,
--   $$
--
--   with no hypothesis at all. This strengthens `Grothendieck.reducedIntegrand_eq_pi_inv_mul_integral`, which assumed both columns nonzero; that hypothesis is unnecessary because when a column vanishes the inner product $\langle X,Y\rangle$ vanishes too, so both sides are $0$ (the left side because Lean's convention $0^{-1}=0$ makes the normalized vector $0$).
--
--   Why it matters: the Fubini step of the substitution chain has to apply this identity at every $W$ in the support of the Gaussian law, and an almost-everywhere statement would force a separate argument that a Gaussian column is nonzero almost surely. With the identity unconditional, no measurable-null-set bookkeeping is needed at this point — the only remaining obligation of the Fubini step is the integrability of the uncurried integrand, which is bounded by $\pi$ through $\lvert\langle X,Y\rangle\rvert\le\lVert X\rVert\lVert Y\rVert$.
--
--   **Formalization Note** Supporting lemma for Lemma 2.1, not a verbatim statement of the paper.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Algorithm A (p. 82), Lemma 2.1 (p. 84).

import Mathlib
import Definitions.Def_Grothendieck_Reduced

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The Laplace form of the rounding integrand, unconditionally.** For every `W`,
`reducedIntegrand r W = π⁻¹ ⟨X,Y⟩ ∫₀^∞∫₀^∞ (st)^{-1/2} e^{-(s‖X‖²+t‖Y‖²)}`; the degenerate cases
where a column vanishes satisfy it too, because both sides are `0`. -/
theorem reducedIntegrand_eq_pi_inv_mul_integral_all (r : ℕ)
    (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = Real.pi⁻¹ * (inner ℝ (colFun r 0 W) (colFun r 1 W) *
          ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2))) := by sorry

end Grothendieck
