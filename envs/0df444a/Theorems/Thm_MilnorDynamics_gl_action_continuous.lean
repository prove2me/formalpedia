-- Prove2me | Theorems.Thm_MilnorDynamics_gl_action_continuous
-- name    : MilnorDynamics.gl_action_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T03:17:50.897626+00:00
-- url     : https://prove2.me/theorems/89f531fd-5b9c-4904-9318-8a562cdc91b0
-- title:
--   The Mobius action on the Riemann sphere is continuous, as is its inverse action
-- statement:
--   **Continuity of a Mobius transformation of the sphere.** For every invertible complex $2\times2$ matrix $g$, both the induced fractional linear transformation $x\mapsto g\cdot x$ and its inverse $x\mapsto g^{-1}\cdot x$ are continuous self-maps of the Riemann sphere $\hat{\mathbb C}$ (with the topology of the one-point compactification, in which a sequence escapes to $\infty$ exactly when it eventually leaves every compact subset of $\mathbb C$).
--
--   This is the qualitative companion of the chordal uniform continuity of the same map. Milnor's proof of Theorem 3.7 moves the three omitted values to $0,1,\infty$ by a Mobius transformation and then transfers normality of the normalised family back to the original one; that transfer needs the normalised limit to be carried back to a *continuous* map, which is exactly this continuity statement. In the finite affine chart the map is a fractional linear function and the only work is at the pole, where the one-point compactification topology has to be checked.
--
--   **Formalization Note** The action is `OnePoint.instGLAction`; the two chart formulas are `OnePoint.smul_some_eq_ite` and `OnePoint.smul_infty_eq_ite`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; Mobius transformations are homeomorphisms of the Riemann sphere.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem gl_action_continuous (g : GL (Fin 2) ℂ) :
    Continuous (fun x : OnePoint ℂ => g • x) ∧
      Continuous (fun x : OnePoint ℂ => g⁻¹ • x) := by sorry

end MilnorDynamics
