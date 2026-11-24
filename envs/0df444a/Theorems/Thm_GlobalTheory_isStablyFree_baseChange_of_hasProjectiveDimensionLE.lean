-- Prove2me | Theorems.Thm_GlobalTheory_isStablyFree_baseChange_of_hasProjectiveDimensionLE
-- name    : GlobalTheory.isStablyFree_baseChange_of_hasProjectiveDimensionLE
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:33.119973+00:00
-- url     : https://prove2.me/theorems/7eb04c2c-fa07-4576-8c2d-f01b87384ea5
-- title:
--   Global Theory: is Stably Free base Change of has Projective Dimension LE
-- statement:
--   The Global Theory construction uses the is Stably Free base Change of has Projective Dimension LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsPrincipalMapAwayOfHasProjectiveDimensionLE.lean#L18-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsPrincipalMapAwayOfHasProjectiveDimensionLE.lean#L18-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsPrincipalMapAwayOfHasProjectiveDimensionLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open scoped TensorProduct

theorem GlobalTheory.isStablyFree_baseChange_of_hasProjectiveDimensionLE (R : Type) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Module.Flat R A]
    (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasProjectiveDimensionLE (ModuleCat.of R M) n → Module.Projective A (A ⊗[R] M) →
        Module.IsStablyFree A (A ⊗[R] M) := by sorry
