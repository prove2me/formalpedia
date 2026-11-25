-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ordIn_subset_rangeIn
-- name    : GroundTheory.Arith.SchemeCoh.ordIn_subset_rangeIn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:31.776895+00:00
-- url     : https://prove2.me/theorems/7ddd8073-2d85-4412-b931-cc144c1aedee
-- title:
--   Scheme Coh: ord In subset range In
-- statement:
--   The Scheme Coh construction uses the ord In subset range In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L173-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L173-L174

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

theorem GroundTheory.Arith.SchemeCoh.ordIn_subset_rangeIn {n : ℕ} (S : Set ι) : ordIn (n := n) S ⊆ rangeIn S := by sorry
