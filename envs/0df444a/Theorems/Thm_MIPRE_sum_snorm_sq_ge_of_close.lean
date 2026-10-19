-- Prove2me | Theorems.Thm_MIPRE_sum_snorm_sq_ge_of_close
-- name    : MIPRE.sum_snorm_sq_ge_of_close
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:15:36.535385+00:00
-- url     : https://prove2.me/theorems/ce1e4766-8702-46ce-8c26-90b1c40be1b5
-- title:
--   Close measurements have close values, at the level of vectors (the paper's fact:approx-implies-close-value, NW19's Fact 4.31): two families of operators whose total squared…
-- statement:
--   A statement of the module `MIPRE.Foundations.OracularTensor` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of oracularization, for bipartite strategies. Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness-tensor`), at the level of games and for **arbitrary tensor-product strategies**: a strategy of value at least `1 - ε` for `MIPRE.SeededGame.oracular` yields one of value at least `1 - 24√ε` for the input game, and so `val*` of the oracularization above `1 - ε` puts `val*` of the input at least `1 - 24√ε`. `MIPRE/Foundations/OracularSound.lean` proves the same bound for *synchronous* strategies. That is not the statement a verifier-level consumer can use:…
--
--   **Close measurements have close values**, at the level of vectors (the paper's
--   `fact:approx-implies-close-value`, NW19's Fact 4.31): two families of operators whose total
--   squared mass on `v` is at most one put masses within `2√δ` of each other on any set of outcomes,
--   `δ` their summed squared deviation. For projections the squared mass is the Born probability.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N : Type*} [Fintype N] {ι : Type*} [Fintype ι]
--
--   theorem MIPRE.sum_snorm_sq_ge_of_close (v : N → ℂ) (R O : ι → Matrix N N ℂ)
--       (hR : ∑ i, snorm v (R i) ^ 2 ≤ 1) (hO : ∑ i, snorm v (O i) ^ 2 ≤ 1) (acc : Finset ι) :
--       ∑ i ∈ acc, snorm v (O i) ^ 2 - 2 * √(∑ i, snorm v (R i - O i) ^ 2)
--         ≤ ∑ i ∈ acc, snorm v (R i) ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.sum_snorm_sq_ge_of_close` is declared in `MIPRE/Foundations/OracularTensor.lean`, lines 91–140. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularTensor.lean#L91-L140

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
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N] {ι : Type*} [Fintype ι]

theorem MIPRE.sum_snorm_sq_ge_of_close (v : N → ℂ) (R O : ι → Matrix N N ℂ)
    (hR : ∑ i, snorm v (R i) ^ 2 ≤ 1) (hO : ∑ i, snorm v (O i) ^ 2 ≤ 1) (acc : Finset ι) :
    ∑ i ∈ acc, snorm v (O i) ^ 2 - 2 * √(∑ i, snorm v (R i - O i) ^ 2)
      ≤ ∑ i ∈ acc, snorm v (R i) ^ 2 := by sorry
