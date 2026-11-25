-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_ker_cotMap_of_ker_eq
-- name    : GlobalTheory.PDivGroup.ker_cotMap_of_ker_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:45.046531+00:00
-- url     : https://prove2.me/theorems/40d55bd9-0173-4e3a-9e0f-ff34fd24186a
-- title:
--   PDiv Group: ker cot Map of ker eq
-- statement:
--   The PDiv Group construction uses the ker cot Map of ker eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DUnitMemRangeOfMemKerIdeal.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DUnitMemRangeOfMemKerIdeal.lean#L78-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Coalgebra Bialgebra WithConv
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)

theorem GlobalTheory.PDivGroup.ker_cotMap_of_ker_eq {m n : ℕ} {f : G.A n →ₐc[O] G.A m} (hf : Function.Surjective f)
    (hk : RingHom.ker f = torsionIdeal O _ (p ^ m)) :
    LinearMap.ker (cotMap f) = Ideal.span {(p : O) ^ m} • (⊤ : Submodule O (Cot O (G.A n))) := by sorry
