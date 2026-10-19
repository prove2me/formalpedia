-- Prove2me | Theorems.Thm_MIPRE_agreeSum_le_sqrt_mul_sqrt
-- name    : MIPRE.agreeSum_le_sqrt_mul_sqrt
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:15.181962+00:00
-- url     : https://prove2.me/theorems/2d0efe0e-6d37-4fbc-9ad0-a72513be07ac
-- title:
--   Cauchy--Schwarz for the agreement: agreeSum ≤ √weightA · √weightB
-- statement:
--   A statement of the module `MIPRE.Foundations.POVMMix` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Mixtures and extensions of POVMs, and the agreement triangle. Three constructions on bundled POVMs that the padded strategy of the Pauli basis test's stage 4 needs, and one inequality. * `POVM.aOp` extends a POVM on `d` by the identity to `d × E`; `POVM.dirac a₀` answers `a₀` with certainty; `POVM.mix w Q` is a convex combination of POVMs with the same outcomes. A strategy that must be a *function of the question* while the analysis controls it *sample by sample* is a mixture over the samples producing the question, and the Born rule's linearity (`bornProb_mix_left`, `bornProb_mix_right`)…
--
--   **Cauchy--Schwarz for the agreement**: `agreeSum ≤ √weightA · √weightB`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
--   variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
--
--   theorem MIPRE.agreeSum_le_sqrt_mul_sqrt (hμ : ∀ x, 0 ≤ μ x) (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
--       agreeSum μ ψ M N ≤ Real.sqrt (weightA μ ψ M) * Real.sqrt (weightB μ ψ N)
--   ```
--
--   **Formalization Note** `MIPRE.agreeSum_le_sqrt_mul_sqrt` is declared in `MIPRE/Foundations/POVMMix.lean`, lines 451–475. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/POVMMix.lean#L451-L475; blueprint lem:qld-global-success

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
import Definitions.Def_MIPRE_Foundations_POVMMix

open MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}

theorem MIPRE.agreeSum_le_sqrt_mul_sqrt (hμ : ∀ x, 0 ≤ μ x) (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    agreeSum μ ψ M N ≤ Real.sqrt (weightA μ ψ M) * Real.sqrt (weightB μ ψ N) := by sorry
