-- Prove2me | Theorems.Thm_MIPRE_sum_snorm_sq_prod_le_one
-- name    : MIPRE.sum_snorm_sq_prod_le_one
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:42:46.698981+00:00
-- url     : https://prove2.me/theorems/ac0c02ad-dab1-4024-bdc0-27d742b82f37
-- title:
--   A mutually orthogonal family of products of commuting projections has its squared state norms summing to at most one
-- statement:
--   A statement of the module `MIPRE.Foundations.Pasting` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pasting two measurements into one. The blueprint's missing piece for `lem:qld-pairs-of-lines`: NW19's Fact 4.35, the paper's `lem:pasting-updated`. One party holds a *joint* projective measurement `A_{a,b}`; the other holds two projective measurements `G_1` and `G_2` whose coarse-grainings along evaluation maps agree with `A`'s two marginals. The conclusion is that `A` agrees with the **sandwich** `J_{g_1, g_2} = G_2^{g_2} G_1^{g_1} G_2^{g_2}`, coarse-grained by evaluating both outcomes. Two facts beyond the sandwich chain of `MIPRE/Foundations/Sandwich.lean` are needed, and they are proved…
--
--   **A mutually orthogonal family of products of commuting projections** has its squared state
--   norms summing to at most one. Alice's factor need not be a measurement in its own right: only
--   self-adjointness, idempotence and orthogonality along the first index are used.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder Kronecker
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--   variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
--   variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}
--
--   theorem MIPRE.sum_snorm_sq_prod_le_one {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
--       [DecidableEq κ] {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) (P : ι → κ → Matrix dA dA ℂ)
--       (Q : κ → Matrix dB dB ℂ) (hPsa : ∀ i k, (P i k)ᴴ = P i k)
--       (hPidem : ∀ i k, P i k * P i k = P i k)
--       (hPorth : ∀ (i j : ι) (k : κ), i ≠ j → P i k * P j k = 0) (hQ : IsPVM Q) :
--       ∑ i, ∑ k, snorm ψ ((aOp (P i k) : Matrix (dA × dB) _ ℂ) * bOp (Q k)) ^ 2 ≤ 1
--   ```
--
--   **Formalization Note** `MIPRE.sum_snorm_sq_prod_le_one` is declared in `MIPRE/Foundations/Pasting.lean`, lines 553–583. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pasting.lean#L553-L583; blueprint lem:pasting-updated

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
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}

theorem MIPRE.sum_snorm_sq_prod_le_one {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) (P : ι → κ → Matrix dA dA ℂ)
    (Q : κ → Matrix dB dB ℂ) (hPsa : ∀ i k, (P i k)ᴴ = P i k)
    (hPidem : ∀ i k, P i k * P i k = P i k)
    (hPorth : ∀ (i j : ι) (k : κ), i ≠ j → P i k * P j k = 0) (hQ : IsPVM Q) :
    ∑ i, ∑ k, snorm ψ ((aOp (P i k) : Matrix (dA × dB) _ ℂ) * bOp (Q k)) ^ 2 ≤ 1 := by sorry
