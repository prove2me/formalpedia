-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Converse_mem_normGroup_of_isSquare
-- name    : GlobalTheory.QuadSymbol.Converse.mem_normGroup_of_isSquare
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:38.143843+00:00
-- url     : https://prove2.me/theorems/cdfb9022-b2bc-4e57-bcb3-c7a14e93c36f
-- title:
--   Converse: mem norm Group of is Square
-- statement:
--   The Converse construction uses the mem norm Group of is Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEverywhereNormDivOfEtaProdEqOne.lean#L147-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsEverywhereNormDivOfEtaProdEqOne.lean#L147-L152

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

theorem GlobalTheory.QuadSymbol.Converse.mem_normGroup_of_isSquare [CharZero K] (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : K}
    (hδ : δ ≠ 0) (h1 : e 1 * e 1 = algebraMap K L δ) {A : Type} [Field A] [Algebra K A]
    (h : IsSquare (algebraMap K A δ)) (z : Aˣ) : z ∈ normGroup K L A := by sorry
