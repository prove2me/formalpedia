-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_integers_localisation_iff_sum_cmData
-- name    : GlobalTheory.T.mem_integers_localisation_iff_sum_cmData
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:52:46.914461+00:00
-- url     : https://prove2.me/theorems/70992000-8cf2-4c5b-9f0f-3cb45878939b
-- title:
--   T: mem integers localisation iff sum cm Data
-- statement:
--   The T construction uses the mem integers localisation iff sum cm Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIntegersLocalisationIffSumCmDataStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIntegersLocalisationIffSumCmDataStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmData
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmDataStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_integers_localisation_iff_sum_cmData : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), ∀ y : A.Ep, y ∈ A.O ↔ ∃ (n : ℕ) (c : Fin n → 𝒪[A.Fp]) (x : Fin n → 𝓞 E), y = ∑ i, algebraMap A.Fp A.Ep (c i : A.Fp) * A.ιE (x i : E) := by sorry
