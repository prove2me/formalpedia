-- Prove2me | Theorems.Thm_MIPStarRE_Quantum_conicFunctionalDualFeasible_normalizedSeparator
-- name    : MIPStarRE.Quantum.conicFunctionalDualFeasible_normalizedSeparator
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:17:43.749688+00:00
-- url     : https://prove2.me/theorems/451a1630-f89b-46bc-963a-6b6c40169d11
-- title:
--   The normalized constraint functional associated to a separator is feasible for the functional dual problem of the conic image
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteConicDuality` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Finite conic-duality separation lemmas. This module contains the product-space part of the finite-dimensional conic duality argument used by the Section 9 SDP. A separator on a product space `E × ℝ` decomposes into a constraint-coordinate functional and an objective coefficient. If the separator is nonnegative on a conic image and negative at a point with the same constraint coordinate but larger objective coordinate, then the objective coefficient is negative. After normalizing by this negative coefficient one obtains the functional dual bound. The matrix trace-pairing representation and the…
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   The normalized constraint functional associated to a separator is feasible
--   for the functional dual problem of the conic image.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.Quantum
--
--   theorem MIPStarRE.Quantum.conicFunctionalDualFeasible_normalizedSeparator
--       {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F]
--       {C : Set (F × ℝ)}
--       (φ : StrongDual ℝ (F × ℝ))
--       (hφ : ∀ z ∈ C, 0 ≤ φ z)
--       (hcoeff : conicSeparatorObjectiveCoefficient φ < 0) :
--       ∀ z ∈ C, z.2 ≤ conicNormalizedSeparatorFunctional φ z.1
--   ```
--
--   **Formalization Note** `MIPStarRE.Quantum.conicFunctionalDualFeasible_normalizedSeparator` is declared in `MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean`, lines 146–168. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean#L146-L168

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality

open MIPStarRE
open MIPStarRE.Quantum
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.Quantum.conicFunctionalDualFeasible_normalizedSeparator
    {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module ℝ F]
    {C : Set (F × ℝ)}
    (φ : StrongDual ℝ (F × ℝ))
    (hφ : ∀ z ∈ C, 0 ≤ φ z)
    (hcoeff : conicSeparatorObjectiveCoefficient φ < 0) :
    ∀ z ∈ C, z.2 ≤ conicNormalizedSeparatorFunctional φ z.1 := by sorry
