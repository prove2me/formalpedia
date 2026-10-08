-- Prove2me | Theorems.Thm_OAI_LittleFinitistic_extreme_left_right_asymmetry
-- name    : OAI.LittleFinitistic.extreme_left_right_asymmetry
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:53.923304+00:00
-- url     : https://prove2.me/theorems/8062358b-a0f9-44e3-a316-c37ed893eb60
-- statement:
--   The theorem states that there exists a ring Λ in the lowest universe, equipped with a ℂ-algebra structure and finite-dimensional over ℂ, whose left-module and right-module finitistic invariants are as asymmetric as possible. Here, for a ring A, the little finitistic dimension is the supremum of projective dimensions of finitely generated A-modules (in ModuleCat A) whose projective dimension is finite, and the big finitistic dimension is the supremum of projective dimensions of all A-modules with finite projective dimension; both take values in WithBot ℕ∞. The theorem asserts that for Λ both of these equal ⊤, while for the opposite ring Λᵐᵒᵖ both equal 0. It further asserts a failure of the injective generation property for Λ but its validity for Λᵐᵒᵖ. InjectivesGenerate A means that, in the derived category of A-modules, every full subcategory that is closed under isomorphisms, triangulated, and closed under coproducts (colimits of discrete families indexed by any type in the module universe), and that contains every injective module placed in degree 0, contains all objects. So the theorem states that ¬InjectivesGenerate Λ while InjectivesGenerate Λᵐᵒᵖ holds.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FinitisticAsymmetry.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FinitisticAsymmetry.lean; bytes 913..1298
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_FinitisticAsymmetry

namespace OAI

noncomputable section

open CategoryTheory

namespace LittleFinitistic

universe u

variable (A : Type u) [Ring A]

theorem extreme_left_right_asymmetry :
    ∃ (Λ : Type) (_ : Ring Λ) (_ : Algebra ℂ Λ),
      FiniteDimensional ℂ Λ ∧
      littleFinitisticDimension Λ = ⊤ ∧ bigFinitisticDimension Λ = ⊤ ∧
      littleFinitisticDimension Λᵐᵒᵖ = 0 ∧ bigFinitisticDimension Λᵐᵒᵖ = 0 ∧
      ¬ InjectivesGenerate Λ ∧ InjectivesGenerate Λᵐᵒᵖ := by
  sorry

end LittleFinitistic
end
end OAI
