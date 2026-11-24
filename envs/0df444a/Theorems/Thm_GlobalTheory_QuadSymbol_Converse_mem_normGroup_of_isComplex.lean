-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Converse_mem_normGroup_of_isComplex
-- name    : GlobalTheory.QuadSymbol.Converse.mem_normGroup_of_isComplex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:46.708969+00:00
-- url     : https://prove2.me/theorems/08a1f9c1-a0c8-4509-b9e1-16cfcd3fd682
-- title:
--   Converse: mem norm Group of is Complex
-- statement:
--   The Converse construction uses the mem norm Group of is Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEverywhereNormDivOfEtaProdEqOne.lean#L139-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEverywhereNormDivOfEtaProdEqOne.lean#L139-L145

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
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.HilbertRecip
open GlobalTheory.QuadSymbol.Converse
variable {K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]

theorem GlobalTheory.QuadSymbol.Converse.mem_normGroup_of_isComplex (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : K}
    (h1 : e 1 * e 1 = algebraMap K L δ) {w : InfinitePlace K} (h : w.IsComplex)
    (z : (w.Completion)ˣ) : z ∈ normGroup K L w.Completion := by sorry
