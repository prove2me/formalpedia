-- Prove2me | Theorems.Thm_MIPStarRE_Quantum_conicSeparatorObjectiveCoefficient_neg_of_above
-- name    : MIPStarRE.Quantum.conicSeparatorObjectiveCoefficient_neg_of_above
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:17:45.8782+00:00
-- url     : https://prove2.me/theorems/a75f51e1-7a3b-4117-9dcd-37f653a7601b
-- title:
--   If a separator is nonnegative on a conic image point (y, s) and negative at (y, t) with s < t, then its objective-coordinate coefficient is negative
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteConicDuality` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Finite conic-duality separation lemmas. This module contains the product-space part of the finite-dimensional conic duality argument used by the Section 9 SDP. A separator on a product space `E × ℝ` decomposes into a constraint-coordinate functional and an objective coefficient. If the separator is nonnegative on a conic image and negative at a point with the same constraint coordinate but larger objective coordinate, then the objective coefficient is negative. After normalizing by this negative coefficient one obtains the functional dual bound. The matrix trace-pairing representation and the…
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   If a separator is nonnegative on a conic image point `(y, s)` and negative
--   at `(y, t)` with `s < t`, then its objective-coordinate coefficient is
--   negative.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.Quantum
--
--   theorem MIPStarRE.Quantum.conicSeparatorObjectiveCoefficient_neg_of_above
--       {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
--       {C : Set (E × ℝ)}
--       (φ : StrongDual ℝ (E × ℝ))
--       {y : E} {s t : ℝ}
--       (hφ : ∀ z ∈ C, 0 ≤ φ z)
--       (hys : (y, s) ∈ C)
--       (hyt : φ (y, t) < 0)
--       (hst : s < t) :
--       conicSeparatorObjectiveCoefficient φ < 0
--   ```
--
--   **Formalization Note** `MIPStarRE.Quantum.conicSeparatorObjectiveCoefficient_neg_of_above` is declared in `MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean`, lines 65–95. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean#L65-L95

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality

open MIPStarRE
open MIPStarRE.Quantum
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.Quantum.conicSeparatorObjectiveCoefficient_neg_of_above
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {C : Set (E × ℝ)}
    (φ : StrongDual ℝ (E × ℝ))
    {y : E} {s t : ℝ}
    (hφ : ∀ z ∈ C, 0 ≤ φ z)
    (hys : (y, s) ∈ C)
    (hyt : φ (y, t) < 0)
    (hst : s < t) :
    conicSeparatorObjectiveCoefficient φ < 0 := by sorry
