-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_mem_support_projCycle
-- name    : GlobalTheory.ChowHt.mem_support_projCycle
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:20:09.428364+00:00
-- url     : https://prove2.me/theorems/3429ddd8-0eac-52eb-be4b-d25e2a9f4e72
-- title:
--   Chow Ht: mem support proj Cycle
-- statement:
--   The Chow Ht construction uses the mem support proj Cycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L75-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsMultiHomogeneousFixFirstBlock_b3ed944b577456bc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ChowHt
variable {k : Type} [Field k] {N : ℕ}

theorem GlobalTheory.ChowHt.mem_support_projCycle {J Q : Ideal (MvPolynomial (Fin N) k)} :
    Q ∈ (projCycle J).support ↔ Q ∈ projComponents J := by sorry
