-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ordIn_subset_ordFrom
-- name    : GroundTheory.Arith.SchemeCoh.ordIn_subset_ordFrom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:41.298911+00:00
-- url     : https://prove2.me/theorems/44f85b02-4765-4b4f-b02f-c986a6a1150d
-- title:
--   Scheme Coh: ord In subset ord From
-- statement:
--   The Scheme Coh construction uses the ord In subset ord From property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L258-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L258-L264

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

theorem GroundTheory.Arith.SchemeCoh.ordIn_subset_ordFrom {n m : ℕ} (i : Fin (m + 1) → ι) :
    ordIn (n := n) (Set.range i) ⊆ ordFrom (minIdx i) := by sorry
