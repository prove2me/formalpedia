-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_chain_comap_eq
-- name    : GlobalTheory.SatakeWeyl.chain_comap_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:48:36.508088+00:00
-- url     : https://prove2.me/theorems/bab03d4a-2332-4101-a080-5864e4d2fd73
-- title:
--   Satake Weyl: chain comap eq
-- statement:
--   The Satake Weyl construction uses the chain comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContractingAutomorphismSubgroupChainIndex.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContractingAutomorphismSubgroupChainIndex.lean#L9-L20

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

theorem GlobalTheory.SatakeWeyl.chain_comap_eq {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom = (U.map c.toMonoidHom).comap (c ^ (j + 1)).toMonoidHom := by sorry
