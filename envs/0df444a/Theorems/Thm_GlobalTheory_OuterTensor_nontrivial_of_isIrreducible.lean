-- Prove2me | Theorems.Thm_GlobalTheory_OuterTensor_nontrivial_of_isIrreducible
-- name    : GlobalTheory.OuterTensor.nontrivial_of_isIrreducible
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:53.016581+00:00
-- url     : https://prove2.me/theorems/28734978-9886-445e-9d3b-2698e84ef04a
-- title:
--   Outer Tensor: nontrivial of is Irreducible
-- statement:
--   The Outer Tensor construction uses the nontrivial of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleOuterTprod.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsIrreducibleOuterTprod.lean#L7-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpanRangeEqTopOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleOuterTprod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.OuterTensor

theorem GlobalTheory.OuterTensor.nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by sorry
