-- Prove2me | Theorems.Thm_GlobalTheory_span_natCast_dvd_differentIdeal_sq
-- name    : GlobalTheory.span_natCast_dvd_differentIdeal_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:22.507981+00:00
-- url     : https://prove2.me/theorems/9a509847-2c9b-4dbf-9b9e-4817dada3952
-- title:
--   Global Theory: span nat Cast dvd different Ideal sq
-- statement:
--   The Global Theory construction uses the span nat Cast dvd different Ideal sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNatCastMemDifferentIdealPowLe.lean#L21-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNatCastMemDifferentIdealPowLe.lean#L21-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNatCastMemDifferentIdealPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Pointwise
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem GlobalTheory.span_natCast_dvd_differentIdeal_sq (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (N : ℕ)
    (hN0 : 0 < N) (hN : ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E))
    (hmin : ∀ M : ℕ, 0 < M → M < N → ((M : ℕ) : 𝓞 E) ∉ differentIdeal ℤ (𝓞 E)) :
    Ideal.span {((N : ℕ) : 𝓞 E)} ∣ differentIdeal ℤ (𝓞 E) ^ 2 := by sorry
