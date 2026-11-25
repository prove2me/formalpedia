-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_projCycle_apply_of_notMem
-- name    : GlobalTheory.ChowHt.projCycle_apply_of_notMem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:13:50.608702+00:00
-- url     : https://prove2.me/theorems/73cd3fe2-6aac-4df2-a2a2-ea2a3a8efa09
-- title:
--   Chow Ht: proj Cycle apply of not Mem
-- statement:
--   The Chow Ht construction uses the proj Cycle apply of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L70-L73

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

theorem GlobalTheory.ChowHt.projCycle_apply_of_notMem {J Q : Ideal (MvPolynomial (Fin N) k)}
    (h : Q ∉ projComponents J) : projCycle J Q = 0 := by sorry
