-- Prove2me | Theorems.Thm_GlobalTheory_exists_base_near_of_dec_fixed
-- name    : GlobalTheory.exists_base_near_of_dec_fixed
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:44:38.437902+00:00
-- url     : https://prove2.me/theorems/0261b27f-fcbb-5b36-ad1b-8216ffef5dfb
-- title:
--   Global Theory: exists base near of dec fixed
-- statement:
--   The Global Theory construction uses the exists base near of dec fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBaseNearOfDecompositionFixed.lean#L14-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBaseNearOfDecompositionFixed.lean#L14-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlgebraMapSubEqSumConjugatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjPlacesOfSamePrimeBelowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CrtApproxIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBaseNearOfDecompositionFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise
open GlobalTheory

theorem GlobalTheory.exists_base_near_of_dec_fixed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (z : Ω), (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r := by sorry
