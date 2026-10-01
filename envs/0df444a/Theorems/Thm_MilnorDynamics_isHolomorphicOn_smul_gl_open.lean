-- Prove2me | Theorems.Thm_MilnorDynamics_isHolomorphicOn_smul_gl_open
-- name    : MilnorDynamics.isHolomorphicOn_smul_gl_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T09:41:32.620172+00:00
-- url     : https://prove2.me/theorems/69100a80-55f0-4b04-9600-7d39b8c35ebd
-- title:
--   Postcomposing a holomorphic map on an open set with a Mobius map stays holomorphic
-- statement:
--   **Mobius postcomposition preserves holomorphy on the sphere.** Let $U\subseteq\mathbb C$ be an open set, let $f:\mathbb C\to\hat{\mathbb C}$ be holomorphic on $U$ in the chart-wise sense of `IsHolomorphicOn`, and let $g$ be an invertible complex $2\times2$ matrix acting on the sphere by fractional linear transformation. Then the postcomposed map $z\mapsto g\cdot f(z)$ is again holomorphic on $U$.
--
--   This is the algebraic half of the Mobius normalisation step in Milnor's proof of Theorem 3.7: in the two standard affine charts of the sphere, both a Mobius transformation and its inverse are given by rational functions with nonvanishing denominators, so composing a chart-wise holomorphic map with one keeps it chart-wise holomorphic, and continuity of the Mobius action gives continuity on the sphere. It is what makes the normalised family consist of maps to which the theorem applies.
--
--   **Why `IsOpen U` is carried explicitly.** `IsHolomorphicOn`'s two differentiability clauses assert `DifferentiableAt` (an ambient-neighbourhood derivative) at each point of `U`. For a non-open `U` those clauses constrain `f` only at the points of `U`, while the conclusion constrains the composite in a full neighbourhood of each such point; the corresponding hypothesis-free statement is therefore false (counterexample: `U = {0}`, `g = !![0, 1; 1, 1]`, `f w = if w ∈ {1/n : n ≥ 1} then ∞ else ↑(w ^ 2)` satisfies `IsHolomorphicOn {0} f` but `chartFinite (g • f w)` is discontinuous at `0`). With `IsOpen U` the statement is Milnor's chart bookkeeping step and is true; the openness is also exactly what the parent `MilnorDynamics.montel_three_omitted_values` supplies (`hU : IsOpen U`).
--
--   **Formalization Note** The Mobius action is `OnePoint.instGLAction`; the chart formulas are `OnePoint.smul_some_eq_ite` and `OnePoint.smul_infty_eq_ite`. The four chart-transfer identities used by the proof are unconditional in Lean because `chartFinite ∞ = 0` and `chartInfinite 0 = 0` are junk values and division by zero is zero; continuity of the composite is `(gl_action_continuous g).1.comp_continuousOn hf.1`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; holomorphy of rational functions and of chart transitions of the Riemann sphere.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem isHolomorphicOn_smul_gl_open (g : GL (Fin 2) ℂ) (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → OnePoint ℂ) (hf : IsHolomorphicOn U f) :
    IsHolomorphicOn U (fun z => g • f z) := by sorry

end MilnorDynamics
