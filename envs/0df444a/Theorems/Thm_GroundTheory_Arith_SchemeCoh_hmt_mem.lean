-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_hmt_mem
-- name    : GroundTheory.Arith.SchemeCoh.hmt_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:07.73727+00:00
-- url     : https://prove2.me/theorems/f9b9140b-0e91-40b5-b49c-ab58ff126a10
-- title:
--   Scheme Coh: hmt mem
-- statement:
--   The Scheme Coh construction uses the hmt mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L361-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L361-L367

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
variable [LinearOrder ι]

theorem GroundTheory.Arith.SchemeCoh.hmt_mem : ∀ (n : ℕ) (i : Fin (n + 1) → ι),
    hmt n i ∈ Finsupp.supported ℤ ℤ (rangeIn (Set.range i))
  := by sorry
