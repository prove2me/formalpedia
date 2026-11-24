-- Prove2me | Theorems.Thm_GlobalTheory_HilbertRecip_exists_not_mem_nrm_iff
-- name    : GlobalTheory.HilbertRecip.exists_not_mem_nrm_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:48.964684+00:00
-- url     : https://prove2.me/theorems/5ade5f39-a7c2-4bba-ba39-ebd940e22f76
-- title:
--   Hilbert Recip: exists not mem nrm iff
-- statement:
--   The Hilbert Recip construction uses the exists not mem nrm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEverywhereNormDivOfEtaProdEqOne.lean#L14-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEverywhereNormDivOfEtaProdEqOne.lean#L14-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEverywhereNormDivOfEtaProdEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex
noncomputable section
open GlobalTheory GlobalTheory.HilbertRecip
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HilbertRecip.exists_not_mem_nrm_iff {b : Fˣ} (L : Finset (Place F)) (hb : ∀ p ∈ L, b ∉ sqr p)
    (hev : Even L.card) : ∃ a : Fˣ, ∀ p, a ∉ nrm p b ↔ p ∈ L := by sorry
