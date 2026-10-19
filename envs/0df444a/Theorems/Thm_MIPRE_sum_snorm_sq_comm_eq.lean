-- Prove2me | Theorems.Thm_MIPRE_sum_snorm_sq_comm_eq
-- name    : MIPRE.sum_snorm_sq_comm_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:42:34.974981+00:00
-- url     : https://prove2.me/theorems/e3179530-00b5-457f-a710-ae55c6ff22f4
-- title:
--   The commutator sum of two projective families on Bob's factor, written as the deficit of one overlap
-- statement:
--   A statement of the module `MIPRE.Foundations.Pasting` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pasting two measurements into one. The blueprint's missing piece for `lem:qld-pairs-of-lines`: NW19's Fact 4.35, the paper's `lem:pasting-updated`. One party holds a *joint* projective measurement `A_{a,b}`; the other holds two projective measurements `G_1` and `G_2` whose coarse-grainings along evaluation maps agree with `A`'s two marginals. The conclusion is that `A` agrees with the **sandwich** `J_{g_1, g_2} = G_2^{g_2} G_1^{g_1} G_2^{g_2}`, coarse-grained by evaluating both outcomes. Two facts beyond the sandwich chain of `MIPRE/Foundations/Sandwich.lean` are needed, and they are proved…
--
--   The commutator sum of two projective families on Bob's factor, written as the deficit of one
--   overlap. Both the fine-grained and the coarse-grained commutators have this shape, and it is what
--   lets them be compared.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder Kronecker
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--   variable {Z Y G2 R1 R2 : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
--
--   theorem MIPRE.sum_snorm_sq_comm_eq {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
--       {A : R1 → Matrix dB dB ℂ} {B : G2 → Matrix dB dB ℂ} (hA : IsPVM A) (hB : IsPVM B) :
--       ∑ a : R1, ∑ g : G2, snorm ψ (bOp (A a * B g - B g * A a) : Matrix (dA × dB) _ ℂ) ^ 2
--         = 2 - 2 * ∑ a : R1, ∑ g : G2,
--             qform ψ (bOp (A a * B g * A a * B g) : Matrix (dA × dB) _ ℂ)
--   ```
--
--   **Formalization Note** `MIPRE.sum_snorm_sq_comm_eq` is declared in `MIPRE/Foundations/Pasting.lean`, lines 368–428. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pasting.lean#L368-L428; blueprint lem:pasting-updated

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
variable {Z Y G2 R1 R2 : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype G2] [DecidableEq G2] [Fintype R1] [DecidableEq R1]
  [Fintype R2] [DecidableEq R2]

theorem MIPRE.sum_snorm_sq_comm_eq {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 → Matrix dB dB ℂ} {B : G2 → Matrix dB dB ℂ} (hA : IsPVM A) (hB : IsPVM B) :
    ∑ a : R1, ∑ g : G2, snorm ψ (bOp (A a * B g - B g * A a) : Matrix (dA × dB) _ ℂ) ^ 2
      = 2 - 2 * ∑ a : R1, ∑ g : G2,
          qform ψ (bOp (A a * B g * A a * B g) : Matrix (dA × dB) _ ℂ) := by sorry
