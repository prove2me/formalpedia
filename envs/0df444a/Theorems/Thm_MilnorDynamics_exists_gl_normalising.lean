-- Prove2me | Theorems.Thm_MilnorDynamics_exists_gl_normalising
-- name    : MilnorDynamics.exists_gl_normalising
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T02:16:38.97706+00:00
-- url     : https://prove2.me/theorems/98c507cf-bc8d-44c1-9430-2087137bb249
-- title:
--   Mobius normalisation - an invertible 2x2 complex matrix carries any three distinct sphere points to 0, 1 and infinity
-- statement:
--   **The three-transitivity of the Mobius group, in matrix form.** Let $a,b,c$ be three distinct points of the Riemann sphere $\hat{\mathbb C} = \mathbb C \cup \{\infty\}$. Then there is an invertible $2\times 2$ matrix $g$ with complex entries whose induced fractional linear transformation carries
--   $$a \mapsto 0, \qquad b \mapsto 1, \qquad c \mapsto \infty .$$
--
--   This is the reduction that opens Milnor's proof of Theorem 3.7. The Mobius group acts sharply three-transitively on the sphere, so a family of holomorphic maps omitting three arbitrary values $a,b,c$ becomes, after postcomposition with this single normalising map, a family omitting the standard triple $0,1,\infty$. Normality is unaffected because the transformation is a homeomorphism of the sphere. It is stated for the action of $\mathrm{GL}(2,\mathbb C)$ on the one-point compactification of $\mathbb C$, using the identification of the sphere with the projective line.
--
--   **Formalization Note** The action is `OnePoint.instGLAction`, and the targets are the coercions `((0 : ℂ) : OnePoint ℂ)`, `((1 : ℂ) : OnePoint ℂ)` and `∞`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; the sharp three-transitivity of the Mobius group on the Riemann sphere.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem exists_gl_normalising (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g : GL (Fin 2) ℂ,
      g • a = ((0 : ℂ) : OnePoint ℂ) ∧ g • b = ((1 : ℂ) : OnePoint ℂ) ∧ g • c = ∞ := by sorry

end MilnorDynamics
