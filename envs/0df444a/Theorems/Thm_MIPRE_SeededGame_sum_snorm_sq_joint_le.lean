-- Prove2me | Theorems.Thm_MIPRE_SeededGame_sum_snorm_sq_joint_le
-- name    : MIPRE.SeededGame.sum_snorm_sq_joint_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:15:30.442214+00:00
-- url     : https://prove2.me/theorems/e7674fca-9134-44ee-8f79-8c4ad1f4af82
-- title:
--   The three cross-party deviations, each bounded by its role pair's conditional failure, and chained: the product of the two isolated measurements is within 6 times three…
-- statement:
--   A statement of the module `MIPRE.Foundations.OracularTensor` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of oracularization, for bipartite strategies. Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness-tensor`), at the level of games and for **arbitrary tensor-product strategies**: a strategy of value at least `1 - ε` for `MIPRE.SeededGame.oracular` yields one of value at least `1 - 24√ε` for the input game, and so `val*` of the oracularization above `1 - ε` puts `val*` of the input at least `1 - 24√ε`. `MIPRE/Foundations/OracularSound.lean` proves the same bound for *synchronous* strategies. That is not the statement a verifier-level consumer can use:…
--
--   **The three cross-party deviations**, each bounded by its role pair's conditional failure, and
--   chained: the product of the two isolated measurements is within `6` times three conditional
--   failures of the oracle's joint marginal. Linear in the failures; no square root yet.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SeededGame
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
--   variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
--   variable (S : SeededGame V A)
--   variable {S}
--
--   theorem MIPRE.SeededGame.sum_snorm_sq_joint_le (N : TensorProductStrategy S.oracular.toGame) (z : V) :
--       ∑ o : OAns A × OAns A,
--           snorm N.ψ ((aOp (N.PA.M (Role.alice, S.LA z) o.1) :
--               Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
--                 * bOp (N.PB.M (Role.bob, S.LB z) o.2)
--             - aOp (oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2)) ^ 2
--         ≤ 6 * (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
--           + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
--           + N.failAt (Role.oracle, z) (Role.bob, S.LB z))
--   ```
--
--   **Formalization Note** `MIPRE.SeededGame.sum_snorm_sq_joint_le` is declared in `MIPRE/Foundations/OracularTensor.lean`, lines 452–484. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularTensor.lean#L452-L484; blueprint lem:oracular-soundness-model

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
open MIPRE.SeededGame
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
variable {S}
omit [Inhabited A]

theorem MIPRE.SeededGame.sum_snorm_sq_joint_le (N : TensorProductStrategy S.oracular.toGame) (z : V) :
    ∑ o : OAns A × OAns A,
        snorm N.ψ ((aOp (N.PA.M (Role.alice, S.LA z) o.1) :
            Matrix (Fin N.dA × Fin N.dB) (Fin N.dA × Fin N.dB) ℂ)
              * bOp (N.PB.M (Role.bob, S.LB z) o.2)
          - aOp (oracleView N z OAns.aliceView o.1 * oracleView N z OAns.bobView o.2)) ^ 2
      ≤ 6 * (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
        + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
        + N.failAt (Role.oracle, z) (Role.bob, S.LB z)) := by sorry
