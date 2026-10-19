-- Prove2me | Theorems.Thm_MIPRE_sum_stateSqNorm_fourierOf
-- name    : MIPRE.sum_stateSqNorm_fourierOf
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:41:46.215085+00:00
-- url     : https://prove2.me/theorems/36ada89f-6383-4250-8c19-97170c136f5f
-- title:
--   Parseval for a family of operators against a state. The transform is an isometry up to the normalization, so an average bound on the family is a summed bound on the transform…
-- statement:
--   A statement of the module `MIPRE.Foundations.Linearity` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Approximate linearity gives exact linearity. Blueprint `thm:linearity`, the quantum linearity test. A family of observables `{O^u}_{u in F_q^n}` that is *approximately* linear --- `O^u O^{u'}` close to `O^{u + u'}` on average, in the state-dependent distance --- is close on average to a family that is *exactly* linear, after adjoining an ancilla register to one player. The paper imports this from Natarajan--Vidick; it is proved here. The route is the one the blueprint's proof text names, and every step of it is already in this repository: * **Parseval.** The Fourier transform `A_e = |V|^{-1}…
--
--   **Parseval for a family of operators against a state.** The transform is an isometry up to
--   the normalization, so an average bound on the family is a summed bound on the transform and
--   conversely. This is the dictionary between an `F_q`-valued measurement and its binary
--   observables.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix MIPRE.Weyl
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : Type*} [Fintype n] [DecidableEq n]
--   variable {d : Type*} [Fintype d] [DecidableEq d]
--
--   theorem MIPRE.sum_stateSqNorm_fourierOf {dB : Type*} [Fintype dB] [DecidableEq dB]
--       (ψ : d × dB → ℂ) (M : (n → F) → Matrix d d ℂ) :
--       ∑ e : n → F, stateSqNorm ψ (fourierOf M e)
--         = (Fintype.card (n → F) : ℝ)⁻¹ * ∑ a : n → F, stateSqNorm ψ (M a)
--   ```
--
--   **Formalization Note** `MIPRE.sum_stateSqNorm_fourierOf` is declared in `MIPRE/Foundations/Linearity.lean`, lines 192–212. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Linearity.lean#L192-L212; blueprint lem:qld-combined-points

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
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity

open MIPRE
open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem MIPRE.sum_stateSqNorm_fourierOf {dB : Type*} [Fintype dB] [DecidableEq dB]
    (ψ : d × dB → ℂ) (M : (n → F) → Matrix d d ℂ) :
    ∑ e : n → F, stateSqNorm ψ (fourierOf M e)
      = (Fintype.card (n → F) : ℝ)⁻¹ * ∑ a : n → F, stateSqNorm ψ (M a) := by sorry
