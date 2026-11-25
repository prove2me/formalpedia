-- Prove2me | Theorems.Thm_GlobalTheory_HL_GaussSum_norm_gauss_sum_le
-- name    : GlobalTheory.HL.GaussSum.norm_gauss_sum_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:23:47.646244+00:00
-- url     : https://prove2.me/theorems/0151f895-bdca-588e-af9f-f64b67a4eaae
-- title:
--   Gauss Sum: norm gauss sum le
-- statement:
--   The Gauss Sum construction uses the norm gauss sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqNormSumRepsMulIndexLe.lean#L196-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqNormSumRepsMulIndexLe.lean#L196-L369

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GaussSum

theorem GlobalTheory.HL.GaussSum.norm_gauss_sum_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (d i N : ℕ), 1 ≤ i → i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ∀ (χ : AddChar (Fin d → E) ℂ), (∀ u, ‖χ u‖ = 1) → (∀ u : Fin d → E, (∀ a, u a ∈ L.O) → χ (algebraMap F E ((ϖ : F) ^ N) • u) = 1) → ∀ (R : Finset (Fin d → E)) (nrm : (Fin d → E) → F), (∀ u, algebraMap F E (nrm u) = ∑ a, u a * L.cj (u a)) → (∀ u ∈ R, ∀ a, u a ∈ L.O) → (∀ u : Fin d → E, (∀ a, u a ∈ L.O) → ∃! w, w ∈ R ∧ ∀ a, ∃ c ∈ L.O, u a - w a = algebraMap F E ((ϖ : F) ^ N) * c) → ‖∑ u ∈ R, ψ (t * nrm u) * χ u‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(i * d : ℤ)) := by sorry
