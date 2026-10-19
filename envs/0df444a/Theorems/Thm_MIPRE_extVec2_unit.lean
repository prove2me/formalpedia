-- Prove2me | Theorems.Thm_MIPRE_extVec2_unit
-- name    : MIPRE.extVec2_unit
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:51.601842+00:00
-- url     : https://prove2.me/theorems/39968e38-337f-4c8e-b323-f8df6a342d93
-- title:
--   Lemma extVec2_unit of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Sandwich` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The sandwich of two approximately commuting projective measurements. Two projective measurements `{X_a}` and `{Z_b}` on one party that *approximately commute* on a state cannot in general be measured jointly. The **sandwich** `R_{a,b} = Z_b X_a Z_b` always can: it is a POVM --- exactly, by projectivity of `Z` alone --- so its Naimark dilation is a genuine *projective* joint measurement, and the dilation's compression identity carries every Born-rule estimate about `R` to the dilated measurement unchanged. What has to be proved is that the sandwich is approximately self-consistent across the…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder Kronecker
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--   variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]
--
--   theorem MIPRE.extVec2_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : Anc) (b₀ : Bnc) :
--       star (extVec2 ψ a₀ b₀) ⬝ᵥ extVec2 ψ a₀ b₀ = 1
--   ```
--
--   **Formalization Note** `MIPRE.extVec2_unit` is declared in `MIPRE/Foundations/Sandwich.lean`, lines 741–743. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Sandwich.lean#L741-L743; blueprint lem:qld-combined-points

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
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc] [Fintype Bnc] [DecidableEq Bnc]

theorem MIPRE.extVec2_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : Anc) (b₀ : Bnc) :
    star (extVec2 ψ a₀ b₀) ⬝ᵥ extVec2 ψ a₀ b₀ = 1 := by sorry
