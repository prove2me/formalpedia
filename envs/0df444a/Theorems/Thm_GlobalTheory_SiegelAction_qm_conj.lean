-- Prove2me | Theorems.Thm_GlobalTheory_SiegelAction_qm_conj
-- name    : GlobalTheory.SiegelAction.qm_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:11:46.80398+00:00
-- url     : https://prove2.me/theorems/0fc61c90-1b42-40cb-904c-999bdbc3ffbb
-- title:
--   Siegel Action: qm conj
-- statement:
--   The Siegel Action construction uses the qm conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticSiegelActionMemUpperHalfSpaceAndCocycl.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticSiegelActionMemUpperHalfSpaceAndCocycl.lean#L150-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.SiegelAction.qm_conj {α β : Type} (A : Matrix α β ℚ) : (qm A).map conj = qm A := by sorry
