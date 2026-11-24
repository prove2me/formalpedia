-- Prove2me | Theorems.Thm_GlobalTheory_exists_level_of_pairing
-- name    : GlobalTheory.exists_level_of_pairing
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:42.889451+00:00
-- url     : https://prove2.me/theorems/728d7ccd-0df1-48c6-957a-b6ed26b5b366
-- title:
--   Global Theory: exists level of pairing
-- statement:
--   The Global Theory construction uses the exists level of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L112-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsLevelStructureOfWeilPairing.lean#L112-L132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsLevelStructureOfWeilPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open LevelOfPairing

theorem GlobalTheory.exists_level_of_pairing : GlobalFnsSt → WeilSt → MulNSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), IsPrimitiveRoot ze M → (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S), (M : K) ≠ 0 ∧ IsPrimitiveRoot (Units.map s.appTop.hom.toMonoidHom ze) M) → ∀ x : Fin (2 * P.g) → (baseOver S ⟶ P.A), (∀ i, x i ^ M = 1) → (∀ i j, WeilIs P.A P.L M (x i) (x j) (ze ^ stdSymp P.g i j)) → ∃ lev : Level P M ze, lev.pt = x := by sorry
