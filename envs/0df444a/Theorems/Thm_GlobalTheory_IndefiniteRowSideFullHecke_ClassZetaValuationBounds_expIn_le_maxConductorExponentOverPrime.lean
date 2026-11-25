-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ClassZetaValuationBounds_expIn_le_maxConductorExponentOverPrime
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_maxConductorExponentOverPrime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:57.09099+00:00
-- url     : https://prove2.me/theorems/19ae40ee-9e09-4745-894c-72c4ef31248c
-- title:
--   Class Zeta Valuation Bounds: exp In le max Conductor Exponent Over Prime
-- statement:
--   The Class Zeta Valuation Bounds construction uses the exp In le max Conductor Exponent Over Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/VpBounds.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/VpBounds.lean#L102-L104

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory.CMVal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds
variable {E : Type} [Field E] [NumberField E]
variable {I : Type} [Fintype I]

theorem GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_maxConductorExponentOverPrime {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) {l : ℕ} {v : HeightOneSpectrum (OF E)}
    (hv : (l : OF E) ∈ v.asIdeal) : expIn 𝔣 v ≤ a0 𝔣 l := by sorry
