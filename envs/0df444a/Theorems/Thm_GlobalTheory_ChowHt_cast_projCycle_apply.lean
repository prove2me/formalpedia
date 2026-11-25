-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_cast_projCycle_apply
-- name    : GlobalTheory.ChowHt.cast_projCycle_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:19:18.503617+00:00
-- url     : https://prove2.me/theorems/8b851241-7017-55be-9da4-4c3a5fb228f1
-- title:
--   Chow Ht: cast proj Cycle apply
-- statement:
--   The Chow Ht construction uses the cast proj Cycle apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L64-L68

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

theorem GlobalTheory.ChowHt.cast_projCycle_apply {J Q : Ideal (MvPolynomial (Fin N) k)} [Q.IsPrime]
    (h : Q ∈ projComponents J) : (projCycle J Q : ℕ∞) = localLength J Q := by sorry
