-- Prove2me | Theorems.Thm_GlobalTheory_LocSpan_mem_O_iff
-- name    : GlobalTheory.LocSpan.mem_O_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:28.844172+00:00
-- url     : https://prove2.me/theorems/9095d3ed-0061-4c14-91bf-d3b6bd95f594
-- title:
--   Loc Span: mem O iff
-- statement:
--   The Loc Span construction uses the mem O iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIntegersLocalisationIffSumCmData.lean#L75-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemIntegersLocalisationIffSumCmData.lean#L75-L132

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmData
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
open GlobalTheory GlobalTheory.LocSpan
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem GlobalTheory.LocSpan.mem_O_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), ∀ y : A.Ep, y ∈ A.O ↔ ∃ (n : ℕ) (c : Fin n → 𝒪[A.Fp]) (x : Fin n → 𝓞 E), y = ∑ i, algebraMap A.Fp A.Ep (c i : A.Fp) * A.ιE (x i : E) := by sorry
