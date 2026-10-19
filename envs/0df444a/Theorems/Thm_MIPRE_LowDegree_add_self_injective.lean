-- Prove2me | Theorems.Thm_MIPRE_LowDegree_add_self_injective
-- name    : MIPRE.LowDegree.add_self_injective
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:07.698852+00:00
-- url     : https://prove2.me/theorems/35fed04f-b862-41eb-9d1d-6d514198a8bd
-- title:
--   In a finite abelian group of odd order, doubling is injective
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.SelfDualize` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Self-dualization in characteristic two. The step that turns a normal basis into a *self-dual* normal basis (blueprint `lem:self-dual-basis`, ledger nodes `1.1.6.1.7` and `1.1.6.1.8`). Written in the group algebra, where the whole step is two short lemmas. If `α` is a normal element of `K / F` with Galois group `G`, the Gram matrix of its orbit is circulant, i.e. it is the element `c ∈ F[G]` with `c g = tr(α · g α)`; it is a unit, and it is fixed by the involution `τ` induced by `g ↦ g⁻¹`. Replacing `α` by `a • α` replaces `c` by `a · τ a · c`, so a self-dual normal basis is exactly a solution…
--
--   In a finite abelian group of odd order, doubling is injective.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open Finset
--   variable {G : Type*} [AddCommGroup G] [Fintype G]
--
--   theorem MIPRE.LowDegree.add_self_injective (hG : Odd (Fintype.card G)) :
--       Function.Injective fun g : G => g + g
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.add_self_injective` is declared in `MIPRE/Foundations/LowDegree/SelfDualize.lean`, lines 56–69. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/SelfDualize.lean#L56-L69

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize

open MIPRE
open MIPRE.LowDegree
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem MIPRE.LowDegree.add_self_injective (hG : Odd (Fintype.card G)) :
    Function.Injective fun g : G => g + g := by sorry
