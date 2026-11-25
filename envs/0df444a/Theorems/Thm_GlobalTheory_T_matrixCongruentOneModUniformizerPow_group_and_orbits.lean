-- Prove2me | Theorems.Thm_GlobalTheory_T_matrixCongruentOneModUniformizerPow_group_and_orbits
-- name    : GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:33:10.843798+00:00
-- url     : https://prove2.me/theorems/1f9bbd45-be94-4887-849e-fc57b29c0c26
-- title:
--   T: matrix Congruent One Mod Uniformizer Pow group and orbits
-- statement:
--   The T construction uses the matrix Congruent One Mod Uniformizer Pow group and orbits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m i : ℕ), 1 ≤ i → (1 : Matrix (Fin m) (Fin m) E) ∈ congK L ϖ m i ∧ (∀ A ∈ congK L ϖ m i, IsIntM L A ∧ IsUnit A.det ∧ vE L ϖ (A.det * L.cj A.det) = 0 ∧ A⁻¹ ∈ congK L ϖ m i ∧ (∀ B ∈ congK L ϖ m i, A * B ∈ congK L ϖ m i) ∧ ∀ i' ≥ i, ∀ B ∈ congK L ϖ m i', A⁻¹ * B * A ∈ congK L ϖ m i' ∧ B ∈ congK L ϖ m i) ∧ ∀ Γ : Matrix (Fin m) (Fin m) E, IsHerm L Γ → IsUnit Γ.det → IsCO (hermLat L m) (horb L ϖ Γ i) ∧ 0 < cont (hermLat L m) (horb L ϖ Γ i) := by sorry
