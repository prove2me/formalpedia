-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ClassZetaValuationBounds_expIn_le_two
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_two
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:41.649801+00:00
-- url     : https://prove2.me/theorems/77e63a88-2a07-4be0-97c1-08da1a2b87da
-- title:
--   Class Zeta Valuation Bounds: exp In le two
-- statement:
--   The Class Zeta Valuation Bounds construction uses the exp In le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/VpBounds.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/VpBounds.lean#L97-L100

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_two {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) (v : HeightOneSpectrum (OF E)) : expIn 𝔣 v ≤ 2 := by sorry
