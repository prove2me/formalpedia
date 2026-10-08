-- Prove2me | Theorems.Thm_OAI_LittleFinitistic_Main_exists_counterexample
-- name    : OAI.LittleFinitistic.Main.exists_counterexample
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:53.804629+00:00
-- url     : https://prove2.me/theorems/b73d3ecf-8b52-4602-ae34-522487733d9b
-- statement:
--   The theorem states that there exists a ring A, of type Type (universe level 0), carrying an algebra structure over the complex numbers ℂ, such that A is finite-dimensional as a ℂ-vector space and its little finitistic dimension is ⊤ (infinite). Here littleFinitisticDimension(A) is defined as the supremum, in WithBot ℕ∞, of the projective dimensions of all finitely generated A-modules M (in the category of A-modules at the same universe level) whose projective dimension is strictly less than ⊤, that is, finite. In addition, for every positive natural number m there is a finitely generated A-module N with finite projective dimension (strictly below ⊤) that is at least 2m−2, where 2m−2 is computed as a natural number and then cast to WithBot ℕ∞. Thus the finite projective dimensions of finitely generated modules over A are unbounded. The statement is given as an admitted theorem, with no proof included.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LittleFinitistic.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LittleFinitistic.lean; bytes 540..901
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Definitions.Def_LittleFinitistic

namespace OAI

noncomputable section

open CategoryTheory

namespace LittleFinitistic

universe u

namespace Main

theorem exists_counterexample :
    ∃ (A : Type) (_ : Ring A) (_ : Algebra ℂ A),
      FiniteDimensional ℂ A ∧ littleFinitisticDimension A = ⊤ ∧
        ∀ m : ℕ, 0 < m → ∃ N : ModuleCat.{0} A, Module.Finite A N ∧
          ((2*m-2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension N ∧
            projectiveDimension N < ⊤ := by
  sorry

end Main
end LittleFinitistic
end
end OAI
