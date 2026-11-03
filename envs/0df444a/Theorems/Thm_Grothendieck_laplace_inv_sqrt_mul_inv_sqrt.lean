-- Prove2me | Theorems.Thm_Grothendieck_laplace_inv_sqrt_mul_inv_sqrt
-- name    : Grothendieck.laplace_inv_sqrt_mul_inv_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T21:45:10.061411+00:00
-- url     : https://prove2.me/theorems/585424e9-a9a2-487e-9889-7e0689226e74
-- title:
--   The Laplace step: $\frac{1}{\sqrt A\sqrt B}=\frac1\pi\iint (st)^{-1/2}e^{-(sA+tB)}$
-- statement:
--   For positive reals $A,B$,
--
--   $$
--   \frac{1}{\sqrt A\,\sqrt B}\;=\;\frac1\pi\int_0^\infty\!\!\int_0^\infty (st)^{-1/2}\,e^{-(sA+tB)}\,ds\,dt .
--   $$
--
--   This is the Laplace-transform step of Algorithm A in the paper: the singular factor $1/(\lVert X\rVert\lVert Y\rVert)$ of the rounding expectation is replaced by a smooth two-parameter integral, so that the Gaussian integral over the random matrix can be exchanged with the $s,t$ integrals and evaluated row by row.
--
--   The proof is the one-dimensional Gamma identity $\int_0^\infty u^{-1/2}e^{-Cu}du=\Gamma(1/2)/\sqrt C=\sqrt\pi/\sqrt C$ applied twice. The integrand factorises as $\big(s^{-1/2}e^{-sA}\big)\big(t^{-1/2}e^{-tB}\big)$, so the double integral is the product of the two one-dimensional integrals, $\pi/(\sqrt A\sqrt B)$, and multiplying by $\pi^{-1}$ gives the statement.
--
--   **Formalization Note** A supporting lemma for Lemma 2.1, not a verbatim statement of the paper: the paper applies the Laplace trick without displaying it as an identity.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Algorithm A and its analysis, pp. 82-83; the identity is the Laplace form of $1/\lVert x\rVert$.

import Mathlib

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The Laplace step of the matrix Grothendieck identity.** For `A, B > 0`,
`1/(√A √B) = π⁻¹ ∫₀^∞∫₀^∞ (st)^{-1/2} e^{-(sA+tB)} ds dt`. -/
theorem laplace_inv_sqrt_mul_inv_sqrt {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (Real.sqrt A * Real.sqrt B)⁻¹
      = Real.pi⁻¹ * ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
          (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B)) := by sorry

end Grothendieck
