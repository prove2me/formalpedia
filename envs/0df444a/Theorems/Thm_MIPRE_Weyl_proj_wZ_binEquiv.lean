-- Prove2me | Theorems.Thm_MIPRE_Weyl_proj_wZ_binEquiv
-- name    : MIPRE.Weyl.proj_wZ_binEquiv
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:44:51.922617+00:00
-- url     : https://prove2.me/theorems/ba246ada-56c7-44fc-a9c3-32eaf08a83c4
-- title:
--   The Z-side projectors transport
-- statement:
--   A statement of the module `MIPRE.Foundations.WeylBinary` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). From qudits to qubits: the generalized Pauli system is a qubit Pauli system. Blueprint `lem:pauli-binary`. A self-dual basis of `F_q` over `F_2` identifies `F_q^n` with `F_2^{n x k}`, and under that identification **every piece of the Weyl data over `F_q` becomes the corresponding piece over `F_2`**: the form `trDot`, the two operator families, their spectral projectors, and the maximally entangled state.
--
--   **The `Z`-side projectors transport.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Weyl
--   open Finset Matrix MIPRE MIPRE.LowDegree
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : Type*} [Fintype n] [DecidableEq n]
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι]
--   variable {b : Module.Basis ι (ZMod 2) F}
--
--   theorem MIPRE.Weyl.proj_wZ_binEquiv (hb : IsSelfDualBasis b) (e : n → F) :
--       (proj wZ (binEquiv (n := n) b e)).submatrix (binEquiv b) (binEquiv b)
--         = proj (wZ (F := F) (n := n)) e
--   ```
--
--   **Formalization Note** `MIPRE.Weyl.proj_wZ_binEquiv` is declared in `MIPRE/Foundations/WeylBinary.lean`, lines 114–120. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/WeylBinary.lean#L114-L120; blueprint lem:pauli-binary

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
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
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary

open MIPRE
open MIPRE.Weyl
open Finset Matrix MIPRE MIPRE.LowDegree
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {b : Module.Basis ι (ZMod 2) F}

theorem MIPRE.Weyl.proj_wZ_binEquiv (hb : IsSelfDualBasis b) (e : n → F) :
    (proj wZ (binEquiv (n := n) b e)).submatrix (binEquiv b) (binEquiv b)
      = proj (wZ (F := F) (n := n)) e := by sorry
