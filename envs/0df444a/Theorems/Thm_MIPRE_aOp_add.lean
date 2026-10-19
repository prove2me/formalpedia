-- Prove2me | Theorems.Thm_MIPRE_aOp_add
-- name    : MIPRE.aOp_add
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:24.975523+00:00
-- url     : https://prove2.me/theorems/089cccdb-cf64-4981-9af6-d006955c1b00
-- title:
--   Lemma aOp_add of the MIP* = RE formalization
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
--   theorem MIPRE.aOp_add (X Y : Matrix HA HA ℂ) :
--       aOp (X + Y) = (aOp X : Matrix (HA × HB) _ ℂ) + aOp Y
--   ```
--
--   **Formalization Note** `MIPRE.aOp_add` is declared in `MIPRE/Foundations/OpBound.lean`, lines 314–315. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OpBound.lean#L314-L315

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

theorem MIPRE.aOp_add (X Y : Matrix HA HA ℂ) :
    aOp (X + Y) = (aOp X : Matrix (HA × HB) _ ℂ) + aOp Y := by sorry
