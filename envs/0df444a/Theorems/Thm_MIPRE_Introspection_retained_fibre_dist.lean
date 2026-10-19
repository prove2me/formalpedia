-- Prove2me | Theorems.Thm_MIPRE_Introspection_retained_fibre_dist
-- name    : MIPRE.Introspection.retained_fibre_dist
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:32:34.742775+00:00
-- url     : https://prove2.me/theorems/275343df-e0ff-4de6-b05c-f3d2e8ecc64e
-- title:
--   Keeping the matching target fibre costs twice the marginal error plus twice the original error
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.RetainedFibre` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Retaining a classical fibre after twirling. The consistency marginal lets us retain the matching block of a nearby measurement. An exactly consistent projective mirror moves the rightmost projector to the front, where it is a contraction. No outcome-count factor enters the estimate.
--
--   Keeping the matching target fibre costs twice the marginal error plus twice the original error.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N Y A : Type*} [Fintype N] [DecidableEq N]
--
--   theorem MIPRE.Introspection.retained_fibre_dist (ψ : N → ℂ) (M T : Y × A → Matrix N N ℂ)
--       (P R : Y → Matrix N N ℂ) (hM : IsPVM M) (hR : IsPVM R)
--       (hPR : ∀ y, P y *ᵥ ψ = R y *ᵥ ψ)
--       (hMR : ∀ y a, M (y, a) * R y = R y * M (y, a))
--       (hTR : ∀ y a, T (y, a) * R y = R y * T (y, a)) :
--       (∑ p : Y × A, snorm ψ (M p - T p * P p.1) ^ 2) ≤
--         2 * (∑ y, snorm ψ ((∑ a, M (y, a)) - P y) ^ 2) +
--         2 * (∑ p : Y × A, snorm ψ (M p - T p) ^ 2)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.retained_fibre_dist` is declared in `MIPRE/Foundations/Introspection/RetainedFibre.lean`, lines 45–75. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/RetainedFibre.lean#L45-L75; blueprint lem:pauli-mixing-coordinates

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
import Definitions.Def_MIPRE_Foundations_Pasting

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N Y A : Type*} [Fintype N] [DecidableEq N]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]

theorem MIPRE.Introspection.retained_fibre_dist (ψ : N → ℂ) (M T : Y × A → Matrix N N ℂ)
    (P R : Y → Matrix N N ℂ) (hM : IsPVM M) (hR : IsPVM R)
    (hPR : ∀ y, P y *ᵥ ψ = R y *ᵥ ψ)
    (hMR : ∀ y a, M (y, a) * R y = R y * M (y, a))
    (hTR : ∀ y a, T (y, a) * R y = R y * T (y, a)) :
    (∑ p : Y × A, snorm ψ (M p - T p * P p.1) ^ 2) ≤
      2 * (∑ y, snorm ψ ((∑ a, M (y, a)) - P y) ^ 2) +
      2 * (∑ p : Y × A, snorm ψ (M p - T p) ^ 2) := by sorry
