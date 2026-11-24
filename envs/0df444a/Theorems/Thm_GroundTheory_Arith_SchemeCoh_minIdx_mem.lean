-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_minIdx_mem
-- name    : GroundTheory.Arith.SchemeCoh.minIdx_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:27:57.655818+00:00
-- url     : https://prove2.me/theorems/ab75b13e-827d-4ae9-a9f8-4e12a4783baf
-- title:
--   Scheme Coh: min Idx mem
-- statement:
--   The Scheme Coh construction uses the min Idx mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L250-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L250-L252

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

theorem GroundTheory.Arith.SchemeCoh.minIdx_mem {n : ℕ} (i : Fin (n + 1) → ι) : minIdx i ∈ Set.range i := by sorry
