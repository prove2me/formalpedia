-- Prove2me | Theorems.Thm_MIPRE_bnd_one_of_conjTranspose_mul_self_le
-- name    : MIPRE.bnd_one_of_conjTranspose_mul_self_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:17.819393+00:00
-- url     : https://prove2.me/theorems/08a7a897-5dab-4b9e-b08b-9912513d9f50
-- title:
--   A self-adjoint contraction is bounded by one. The hypothesis is the *matrix* inequality M† M ≤ 1, which is Matrix.PosSemidef of the difference
-- statement:
--   A statement of the module `MIPRE.Foundations.OpBound` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Operator bounds on matrices, by hand. The rigidity arguments of the Pauli basis test's appendix are chains of estimates `‖M |ψ⟩‖ ≤ …`, and the only thing they need about the operators in front is a bound `‖M v‖ ≤ K ‖v‖`. `Bnd M K` is that bound, with the four closure properties the chains use --- sums, products, scalars, and the two sources: a self-adjoint contraction has `Bnd M 1`, and an isometry has `‖M v‖ = ‖v‖` on the nose. This is the `ℓ²` operator norm, spelled as a relation instead of a number. That is deliberate. Mathlib has the norm, through `Matrix.toEuclideanCLM` and the…
--
--   **A self-adjoint contraction is bounded by one.** The hypothesis is the *matrix*
--   inequality `M† M ≤ 1`, which is `Matrix.PosSemidef` of the difference.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N : Type*} [Fintype N]
--   variable [DecidableEq N]
--
--   theorem MIPRE.bnd_one_of_conjTranspose_mul_self_le {M : Matrix N N ℂ}
--       (h : (Mᴴ * M) ≤ (1 : Matrix N N ℂ)) : Bnd M 1
--   ```
--
--   **Formalization Note** `MIPRE.bnd_one_of_conjTranspose_mul_self_le` is declared in `MIPRE/Foundations/OpBound.lean`, lines 232–250. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OpBound.lean#L232-L250

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable [DecidableEq N]

theorem MIPRE.bnd_one_of_conjTranspose_mul_self_le {M : Matrix N N ℂ}
    (h : (Mᴴ * M) ≤ (1 : Matrix N N ℂ)) : Bnd M 1 := by sorry
