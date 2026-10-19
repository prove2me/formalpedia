-- Prove2me | Theorems.Thm_MIPStarRE_Quantum_conicNormalizedSeparatorFunctional_lt_of_sep
-- name    : MIPStarRE.Quantum.conicNormalizedSeparatorFunctional_lt_of_sep
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:17:46.026015+00:00
-- url     : https://prove2.me/theorems/1cf90e90-3400-4142-86f3-b3e1412c1b52
-- title:
--   If a separator is negative at (y, t), then its normalized constraint-coordinate functional is below t at y
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.FiniteConicDuality` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Finite conic-duality separation lemmas. This module contains the product-space part of the finite-dimensional conic duality argument used by the Section 9 SDP. A separator on a product space `E × ℝ` decomposes into a constraint-coordinate functional and an objective coefficient. If the separator is nonnegative on a conic image and negative at a point with the same constraint coordinate but larger objective coordinate, then the objective coefficient is negative. After normalizing by this negative coefficient one obtains the functional dual bound. The matrix trace-pairing representation and the…
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   If a separator is negative at `(y, t)`, then its normalized
--   constraint-coordinate functional is below `t` at `y`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.Quantum
--
--   theorem MIPStarRE.Quantum.conicNormalizedSeparatorFunctional_lt_of_sep
--       {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
--       (φ : StrongDual ℝ (E × ℝ))
--       {y : E} {t : ℝ}
--       (hsep : φ (y, t) < 0)
--       (hcoeff : conicSeparatorObjectiveCoefficient φ < 0) :
--       conicNormalizedSeparatorFunctional φ y < t
--   ```
--
--   **Formalization Note** `MIPStarRE.Quantum.conicNormalizedSeparatorFunctional_lt_of_sep` is declared in `MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean`, lines 170–190. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteConicDuality.lean#L170-L190

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality

open MIPStarRE
open MIPStarRE.Quantum
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.Quantum.conicNormalizedSeparatorFunctional_lt_of_sep
    {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (φ : StrongDual ℝ (E × ℝ))
    {y : E} {t : ℝ}
    (hsep : φ (y, t) < 0)
    (hcoeff : conicSeparatorObjectiveCoefficient φ < 0) :
    conicNormalizedSeparatorFunctional φ y < t := by sorry
