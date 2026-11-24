-- Prove2me | Theorems.Thm_GlobalTheory_unramExt
-- name    : GlobalTheory.unramExt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:42.312797+00:00
-- url     : https://prove2.me/theorems/bb517802-c283-4bdd-82b1-d58b66253ecb
-- title:
--   Global Theory: unram Ext
-- statement:
--   The Global Theory construction uses the unram Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFiniteEtaleLocalSurjectiveOfIsSeparable.lean#L63-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsFiniteEtaleLocalSurjectiveOfIsSeparable.lean#L63-L174

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open Polynomial IsLocalRing

theorem GlobalTheory.unramExt : _root_.ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt := by sorry
