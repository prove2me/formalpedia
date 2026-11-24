-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_mem_rangeIn
-- name    : GroundTheory.Arith.SchemeCoh.lin_mem_rangeIn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:33.74137+00:00
-- url     : https://prove2.me/theorems/7fee7b45-c1df-48c2-93fa-b9242333d961
-- title:
--   Scheme Coh: lin mem range In
-- statement:
--   The Scheme Coh construction uses the lin mem range In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L93-L101

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory
universe w
variable {ι : Type w}

theorem GroundTheory.Arith.SchemeCoh.lin_mem_rangeIn {m n : ℕ} (f : (Fin (m + 1) → ι) → Chain ι n) {S : Set ι}
    (hf : ∀ j : Fin (m + 1) → ι, Set.range j ⊆ S →
      f j ∈ Finsupp.supported ℤ ℤ (rangeIn (n := n) (Set.range j)))
    {c : Chain ι m} (hc : c ∈ Finsupp.supported ℤ ℤ (rangeIn S)) :
    lin f c ∈ Finsupp.supported ℤ ℤ (rangeIn S) := by sorry
