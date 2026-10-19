-- Prove2me | Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt
-- name    : MIPRE.sum_weighted_mul_le_sqrt
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:17:01.877468+00:00
-- url     : https://prove2.me/theorems/cce585b7-0f19-46e0-9652-04e216be9ada
-- title:
--   Cauchy--Schwarz against a weight. The one inequality the chain's square roots come from, and also the Jensen step that moves an average inside a square root (take v = 1)
-- statement:
--   A statement of the module `MIPRE.Foundations.Sandwich` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The sandwich of two approximately commuting projective measurements. Two projective measurements `{X_a}` and `{Z_b}` on one party that *approximately commute* on a state cannot in general be measured jointly. The **sandwich** `R_{a,b} = Z_b X_a Z_b` always can: it is a POVM --- exactly, by projectivity of `Z` alone --- so its Naimark dilation is a genuine *projective* joint measurement, and the dilation's compression identity carries every Born-rule estimate about `R` to the dilated measurement unchanged. What has to be proved is that the sandwich is approximately self-consistent across the…
--
--   **Cauchy--Schwarz against a weight.** The one inequality the chain's square roots come from,
--   and also the Jensen step that moves an average inside a square root (take `v = 1`).
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder Kronecker
--
--   theorem MIPRE.sum_weighted_mul_le_sqrt {ι : Type*} [Fintype ι] (w u v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
--       ∑ i, w i * (u i * v i)
--         ≤ Real.sqrt (∑ i, w i * u i ^ 2) * Real.sqrt (∑ i, w i * v i ^ 2)
--   ```
--
--   **Formalization Note** `MIPRE.sum_weighted_mul_le_sqrt` is declared in `MIPRE/Foundations/Sandwich.lean`, lines 52–87. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Sandwich.lean#L52-L87; blueprint lem:qld-combined-points

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false

theorem MIPRE.sum_weighted_mul_le_sqrt {ι : Type*} [Fintype ι] (w u v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ i, w i * (u i * v i)
      ≤ Real.sqrt (∑ i, w i * u i ^ 2) * Real.sqrt (∑ i, w i * v i ^ 2) := by sorry
