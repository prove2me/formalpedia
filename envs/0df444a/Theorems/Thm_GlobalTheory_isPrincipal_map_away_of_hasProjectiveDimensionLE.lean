-- Prove2me | Theorems.Thm_GlobalTheory_isPrincipal_map_away_of_hasProjectiveDimensionLE
-- name    : GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:59:42.136657+00:00
-- url     : https://prove2.me/theorems/9a3d923b-759b-42cc-b0c3-ebaf63f3fbc6
-- title:
--   Global Theory: is Principal map away of has Projective Dimension LE
-- statement:
--   The Global Theory construction uses the is Principal map away of has Projective Dimension LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsPrincipalMapAwayOfHasProjectiveDimensionLE.lean#L98-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsPrincipalMapAwayOfHasProjectiveDimensionLE.lean#L98-L108

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

theorem GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R) (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ), HasProjectiveDimensionLE (ModuleCat.of R I) n → Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal := by sorry
