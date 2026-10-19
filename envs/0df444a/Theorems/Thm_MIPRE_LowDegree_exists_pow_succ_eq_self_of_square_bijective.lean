-- Prove2me | Theorems.Thm_MIPRE_LowDegree_exists_pow_succ_eq_self_of_square_bijective
-- name    : MIPRE.LowDegree.exists_pow_succ_eq_self_of_square_bijective
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:23:33.672463+00:00
-- url     : https://prove2.me/theorems/53967d96-9418-4cb9-83d9-e08010c21805
-- title:
--   Bijective squaring on a finite ring makes every element periodic under squaring
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.FiniteReducedComponents` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Primitive components of a finite ring with bijective squaring. This supplies the algebraic justification for splitting the binary cyclic group algebra by its fixed vectors. The computations need only multiplication and linear algebra; the finite permutation argument below is a correctness proof, not an enumeration performed by the algorithm.
--
--   Bijective squaring on a finite ring makes every element periodic under squaring.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   variable {R : Type*} [CommRing R] [Finite R]
--
--   theorem MIPRE.LowDegree.exists_pow_succ_eq_self_of_square_bijective
--       (hsq : Function.Bijective (fun x : R => x * x)) (x : R) :
--       ∃ n : ℕ, 0 < n ∧ x ^ (n + 1) = x
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.exists_pow_succ_eq_self_of_square_bijective` is declared in `MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean`, lines 21–43. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean#L21-L43

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents

open MIPRE
open MIPRE.LowDegree
variable {R : Type*} [CommRing R] [Finite R]

theorem MIPRE.LowDegree.exists_pow_succ_eq_self_of_square_bijective
    (hsq : Function.Bijective (fun x : R => x * x)) (x : R) :
    ∃ n : ℕ, 0 < n ∧ x ^ (n + 1) = x := by sorry
