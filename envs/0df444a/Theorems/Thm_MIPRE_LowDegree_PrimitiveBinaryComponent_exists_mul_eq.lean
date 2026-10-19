-- Prove2me | Theorems.Thm_MIPRE_LowDegree_PrimitiveBinaryComponent_exists_mul_eq
-- name    : MIPRE.LowDegree.PrimitiveBinaryComponent.exists_mul_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:23:37.103682+00:00
-- url     : https://prove2.me/theorems/33161976-84d6-487e-b3dd-6aeef765326d
-- title:
--   Every nonzero element supported on a primitive component has an inverse in that component
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.FiniteReducedComponents` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Primitive components of a finite ring with bijective squaring. This supplies the algebraic justification for splitting the binary cyclic group algebra by its fixed vectors. The computations need only multiplication and linear algebra; the finite permutation argument below is a correctness proof, not an enumeration performed by the algorithm.
--
--   Every nonzero element supported on a primitive component has an inverse in that component.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   variable {R : Type*} [CommRing R] [Finite R]
--
--   theorem MIPRE.LowDegree.PrimitiveBinaryComponent.exists_mul_eq
--       (hsq : Function.Bijective (fun x : R => x * x)) {e : R}
--       (he : PrimitiveBinaryComponent e) (x : R) (hx : x ≠ 0) (hex : e * x = x) :
--       ∃ y : R, x * y = e
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.PrimitiveBinaryComponent.exists_mul_eq` is declared in `MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean`, lines 49–80. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean#L49-L80; blueprint lem:effective-normal-element

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents

open MIPRE
open MIPRE.LowDegree
variable {R : Type*} [CommRing R] [Finite R]

theorem MIPRE.LowDegree.PrimitiveBinaryComponent.exists_mul_eq
    (hsq : Function.Bijective (fun x : R => x * x)) {e : R}
    (he : PrimitiveBinaryComponent e) (x : R) (hx : x ≠ 0) (hex : e * x = x) :
    ∃ y : R, x * y = e := by sorry
