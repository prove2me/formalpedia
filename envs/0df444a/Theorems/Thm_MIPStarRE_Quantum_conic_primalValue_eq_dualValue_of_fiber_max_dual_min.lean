-- Prove2me | Theorems.Thm_MIPStarRE_Quantum_conic_primalValue_eq_dualValue_of_fiber_max_dual_min
-- name    : MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:17:51.195983+00:00
-- url     : https://prove2.me/theorems/f388f29d-2bf2-4b30-b70c-5e4ce381998e
-- title:
--   A functional conic zero-gap theorem
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteConicDuality` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Finite conic-duality separation lemmas. This module contains the product-space part of the finite-dimensional conic duality argument used by the Section 9 SDP. A separator on a product space `E × ℝ` decomposes into a constraint-coordinate functional and an objective coefficient. If the separator is nonnegative on a conic image and negative at a point with the same constraint coordinate but larger objective coordinate, then the objective coefficient is negative. After normalizing by this negative coefficient one obtains the functional dual bound. The matrix trace-pairing representation and the…
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   A functional conic zero-gap theorem.
--
--   Let `C` be a closed conic image in `F × ℝ`.  Suppose that, on the fiber over
--   `y`, the value `p` lies in `C` and is maximal among all objective coordinates
--   in that fiber.  Suppose also that `d` is minimal among all continuous
--   real-linear functionals `ψ` satisfying the functional dual inequalities
--   `t ≤ ψ y'` for every `(y', t) ∈ C`.  If weak duality gives `p ≤ d`, then the
--   attained primal and dual values are equal.
--
--   This is the product-space separation argument behind finite-dimensional conic
--   duality.  It deliberately records the closed-image fiber condition through the
--   maximality hypothesis, rather than assuming that fiber recovery is automatic.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.Quantum
--
--   theorem MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min
--       {F : Type*}
--       [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F]
--       [Module ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
--       (C : ProperCone ℝ (F × ℝ))
--       {y : F} {p d : ℝ}
--       (hprimalMem : (y, p) ∈ C)
--       (hprimalMax : ∀ {t : ℝ}, (y, t) ∈ C → t ≤ p)
--       (hdualMin : ∀ ψ : StrongDual ℝ F,
--         (∀ z ∈ C, z.2 ≤ ψ z.1) → d ≤ ψ y)
--       (hweak : p ≤ d) :
--       p = d
--   ```
--
--   **Formalization Note** `MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min` is declared in `MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean`, lines 192–242. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean#L192-L242

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality

open MIPStarRE
open MIPStarRE.Quantum
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.Quantum.conic_primalValue_eq_dualValue_of_fiber_max_dual_min
    {F : Type*}
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F]
    [Module ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    (C : ProperCone ℝ (F × ℝ))
    {y : F} {p d : ℝ}
    (hprimalMem : (y, p) ∈ C)
    (hprimalMax : ∀ {t : ℝ}, (y, t) ∈ C → t ≤ p)
    (hdualMin : ∀ ψ : StrongDual ℝ F,
      (∀ z ∈ C, z.2 ≤ ψ z.1) → d ≤ ψ y)
    (hweak : p ≤ d) :
    p = d := by sorry
