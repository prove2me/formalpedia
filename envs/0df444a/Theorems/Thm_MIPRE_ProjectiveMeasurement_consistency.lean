-- Prove2me | Theorems.Thm_MIPRE_ProjectiveMeasurement_consistency
-- name    : MIPRE.ProjectiveMeasurement.consistency
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:58.345093+00:00
-- url     : https://prove2.me/theorems/bff040a6-0d19-420e-be63-506e910f94bc
-- title:
--   Perfect consistency: against a tracial state, a projective measurement family answers unequal answers to equal questions with probability zero
-- statement:
--   A statement of the module `MIPRE.Foundations.Games` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Games, strategies, and values. This file contains the definitions of blueprint Section 2.1 ("Games, strategies, and values") of the MIP* = RE formalization project: two-player one-round nonlocal games, the three classes of strategies (tensor-product, synchronous, and commuting), the associated values, and the entanglement requirement. The three strategy classes are built on a common skeleton, which this file factors out: a question-indexed family of projective measurements in a complex star algebra (`MIPRE.ProjectiveMeasurement`). Tensor-product strategies instantiate it on two matrix…
--
--   Perfect consistency: against a tracial state, a projective measurement family
--   answers unequal answers to equal questions with probability zero. This is why the
--   "consistent" condition of a PCC strategy (blueprint `def:pcc`) is automatic for
--   synchronous strategies.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.ProjectiveMeasurement
--   open ComplexOrder Kronecker Matrix
--   open scoped MatrixOrder
--   variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--   variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
--   variable [DecidableEq A]
--
--   theorem MIPRE.ProjectiveMeasurement.consistency (P : ProjectiveMeasurement X A 𝒜) (τ : TracialState 𝒜) (x : X)
--       {a b : A} (hab : a ≠ b) : τ (P.M x a * P.M x b) = 0
--   ```
--
--   **Formalization Note** `MIPRE.ProjectiveMeasurement.consistency` is declared in `MIPRE/Foundations/Games.lean`, lines 294–313. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Games.lean#L294-L313

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games

open MIPRE
open MIPRE.ProjectiveMeasurement
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
variable [DecidableEq A]
omit [Fintype X]

theorem MIPRE.ProjectiveMeasurement.consistency (P : ProjectiveMeasurement X A 𝒜) (τ : TracialState 𝒜) (x : X)
    {a b : A} (hab : a ≠ b) : τ (P.M x a * P.M x b) = 0 := by sorry
