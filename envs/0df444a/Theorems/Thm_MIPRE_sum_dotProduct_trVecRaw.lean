-- Prove2me | Theorems.Thm_MIPRE_sum_dotProduct_trVecRaw
-- name    : MIPRE.sum_dotProduct_trVecRaw
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:42:10.077046+00:00
-- url     : https://prove2.me/theorems/7a3f76d0-a4af-4c76-b432-466360b596be
-- title:
--   Lemma sum_dotProduct_trVecRaw of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Parseval` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Parseval for the character transform. The combining stage of the Pauli appendix moves between two descriptions of the same data: an `F_q`-valued measurement `{P_a}` and its **binary observables** `O^r = sum_a (-1)^{tr(ar)} P_a`, one for each `r in F_q`. The two are Fourier transforms of each other, and what the estimates need is that the transform is an **isometry**: a bound on the observables, averaged over `r`, is a bound on the measurement elements, summed over `a`, and conversely. This file is that dictionary, for vectors and for families of matrices applied to a state: * `fourierVec` is…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix MIPRE.Weyl
--   open scoped Kronecker
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : Type*} [Fintype n] [DecidableEq n]
--   variable {N : Type*} [Fintype N] [DecidableEq N]
--   variable {A : Type*} [Fintype A] [DecidableEq A]
--   variable {dA : Type*} [Fintype dA] [DecidableEq dA]
--
--   theorem MIPRE.sum_dotProduct_trVecRaw (T : F → (N → ℂ)) :
--       ∑ r : F, star (trVecRaw T r) ⬝ᵥ trVecRaw T r
--         = (Fintype.card F : ℂ) * ∑ c : F, star (T c) ⬝ᵥ T c
--   ```
--
--   **Formalization Note** `MIPRE.sum_dotProduct_trVecRaw` is declared in `MIPRE/Foundations/Parseval.lean`, lines 253–300. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Parseval.lean#L253-L300

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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval

open MIPRE
open Finset Matrix MIPRE.Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

theorem MIPRE.sum_dotProduct_trVecRaw (T : F → (N → ℂ)) :
    ∑ r : F, star (trVecRaw T r) ⬝ᵥ trVecRaw T r
      = (Fintype.card F : ℂ) * ∑ c : F, star (T c) ⬝ᵥ T c := by sorry
