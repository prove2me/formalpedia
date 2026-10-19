-- Prove2me | Theorems.Thm_MIPRE_LowDegree_mul_self_bijective
-- name    : MIPRE.LowDegree.mul_self_bijective
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:17.6895+00:00
-- url     : https://prove2.me/theorems/bfdcae97-6019-480d-ad92-9d1a846cba77
-- title:
--   Squaring is bijective on F[G] when F has characteristic two and G is a finite abelian group of odd order
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.SelfDualize` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Self-dualization in characteristic two. The step that turns a normal basis into a *self-dual* normal basis (blueprint `lem:self-dual-basis`, ledger nodes `1.1.6.1.7` and `1.1.6.1.8`). Written in the group algebra, where the whole step is two short lemmas. If `α` is a normal element of `K / F` with Galois group `G`, the Gram matrix of its orbit is circulant, i.e. it is the element `c ∈ F[G]` with `c g = tr(α · g α)`; it is a unit, and it is fixed by the involution `τ` induced by `g ↦ g⁻¹`. Replacing `α` by `a • α` replaces `c` by `a · τ a · c`, so a self-dual normal basis is exactly a solution…
--
--   **Squaring is bijective on `F[G]`** when `F` has characteristic two and `G` is a finite
--   abelian group of odd order.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open Finset
--   variable {G : Type*} [AddCommGroup G] [Fintype G]
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq G]
--
--   theorem MIPRE.LowDegree.mul_self_bijective (hF : CharP F 2) (hG : Odd (Fintype.card G)) :
--       Function.Bijective fun x : AddMonoidAlgebra F G => x * x
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.mul_self_bijective` is declared in `MIPRE/Foundations/LowDegree/SelfDualize.lean`, lines 117–131. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/SelfDualize.lean#L117-L131; blueprint lem:group-algebra-selfdualization

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize

open MIPRE
open MIPRE.LowDegree
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq G]

theorem MIPRE.LowDegree.mul_self_bijective (hF : CharP F 2) (hG : Odd (Fintype.card G)) :
    Function.Bijective fun x : AddMonoidAlgebra F G => x * x := by sorry
