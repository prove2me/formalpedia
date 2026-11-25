-- Prove2me | Theorems.Thm_GlobalTheory_T_abelianScheme_eighth_power_of_matrix_action
-- name    : GlobalTheory.T.abelianScheme_eighth_power_of_matrix_action
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:31.225323+00:00
-- url     : https://prove2.me/theorems/68b73341-bc4c-5e93-9a78-3248a87bd8ed
-- title:
--   T: abelian Scheme eighth power of matrix action
-- statement:
--   The T construction uses the abelian Scheme eighth power of matrix action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AbelianSchemeEighthPowerOfMatrixActionStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/AbelianSchemeEighthPowerOfMatrixActionStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AbelianSchemeEighthPowerOfMatrixAction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AbelianSchemeEighthPowerOfMatrixActionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.abelianScheme_eighth_power_of_matrix_action : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsAbelianScheme G → (∀ m, IsMonHom (ρ m)) → (∀ m m', ρ (m * m') = ρ m' ≫ ρ m) → (∀ m m', ρ (m + m') = ρ m * ρ m') → ρ 1 = 𝟙 G → ∃ (A : Over S) (_ : GrpObj A) (pr : Fin 8 → (G ⟶ A)), IsAbelianScheme A ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧ ∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := by sorry
