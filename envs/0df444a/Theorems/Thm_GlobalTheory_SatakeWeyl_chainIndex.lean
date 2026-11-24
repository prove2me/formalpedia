-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_chainIndex
-- name    : GlobalTheory.SatakeWeyl.chainIndex
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:48:21.443936+00:00
-- url     : https://prove2.me/theorems/daf9059f-1bdf-4239-b8e0-1ff281cc11e6
-- title:
--   Satake Weyl: chain Index
-- statement:
--   The Satake Weyl construction uses the chain Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContractingAutomorphismSubgroupChainIndex.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContractingAutomorphismSubgroupChainIndex.lean#L33-L42

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContractingAutomorphismSubgroupChainIndex
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl

theorem GlobalTheory.SatakeWeyl.chainIndex : ChainIndex := by sorry
