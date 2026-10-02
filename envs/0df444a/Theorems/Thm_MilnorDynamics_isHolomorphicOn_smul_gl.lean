-- Prove2me | Theorems.Thm_MilnorDynamics_isHolomorphicOn_smul_gl
-- name    : MilnorDynamics.isHolomorphicOn_smul_gl
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-01T03:13:49.806139+00:00
-- url     : https://prove2.me/theorems/c0cfcaeb-2d13-42ff-9349-c377288a82ea
-- title:
--   Postcomposing a sphere-holomorphic map with a Mobius map stays sphere-holomorphic
-- statement:
--   **Mobius postcomposition preserves holomorphy on the sphere.** Let $U\subseteq\mathbb C$ be open, let $f:\mathbb C\to\hat{\mathbb C}$ be holomorphic on $U$ in the chart-wise sense of `IsHolomorphicOn`, and let $g$ be an invertible complex $2\times2$ matrix, acting on the sphere by fractional linear transformation. Then the postcomposed map
--   $$z\mapsto g\cdot f(z)$$
--   is again holomorphic on $U$.
--
--   This is the algebraic half of the Mobius normalisation step in Milnor's proof of Theorem 3.7: in the two standard affine charts of the sphere, both a Mobius transformation and its inverse are given by rational functions with nonvanishing denominators, so composing a chart-wise holomorphic map with one keeps it chart-wise holomorphic, and continuity of the Mobius action gives continuity on the sphere. It is what makes the normalised family consist of maps to which the theorem applies.
--
--   **Formalization Note** The Mobius action is `OnePoint.instGLAction`; in the finite chart it sends $u$ to $(g_{00}u+g_{01})/(g_{10}u+g_{11})$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; holomorphy of rational functions and of chart transitions of the Riemann sphere.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem isHolomorphicOn_smul_gl (g : GL (Fin 2) ℂ) (U : Set ℂ) (f : ℂ → OnePoint ℂ)
    (hf : IsHolomorphicOn U f) : IsHolomorphicOn U (fun z => g • f z) := by sorry

end MilnorDynamics
