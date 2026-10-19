-- Prove2me | Theorems.Thm_MIPRE_aOp_conjTranspose
-- name    : MIPRE.aOp_conjTranspose
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:24:31.763695+00:00
-- url     : https://prove2.me/theorems/e09c211c-cf0e-43db-823c-ed8f5f404136
-- title:
--   Lemma aOp_conjTranspose of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.OpBound` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Operator bounds on matrices, by hand. The rigidity arguments of the Pauli basis test's appendix are chains of estimates `‖M |ψ⟩‖ ≤ …`, and the only thing they need about the operators in front is a bound `‖M v‖ ≤ K ‖v‖`. `Bnd M K` is that bound, with the four closure properties the chains use --- sums, products, scalars, and the two sources: a self-adjoint contraction has `Bnd M 1`, and an isometry has `‖M v‖ = ‖v‖` on the nose. This is the `ℓ²` operator norm, spelled as a relation instead of a number. That is deliberate. Mathlib has the norm, through `Matrix.toEuclideanCLM` and the…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   open Kronecker
--   variable {N : Type*} [Fintype N]
--   variable [DecidableEq N]
--   variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
--
--   theorem MIPRE.aOp_conjTranspose (X : Matrix HA HA ℂ) :
--       (aOp X : Matrix (HA × HB) _ ℂ)ᴴ = aOp (Xᴴ)
--   ```
--
--   **Formalization Note** `MIPRE.aOp_conjTranspose` is declared in `MIPRE/Foundations/OpBound.lean`, lines 338–340. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OpBound.lean#L338-L340

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_OpBound

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

theorem MIPRE.aOp_conjTranspose (X : Matrix HA HA ℂ) :
    (aOp X : Matrix (HA × HB) _ ℂ)ᴴ = aOp (Xᴴ) := by sorry
