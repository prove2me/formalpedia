-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_hmt_zero
-- name    : GroundTheory.Arith.SchemeCoh.lin_hmt_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:17.845474+00:00
-- url     : https://prove2.me/theorems/61682352-2dd2-4a39-b2cb-e099d920cf6a
-- title:
--   Scheme Coh: lin hmt zero
-- statement:
--   The Scheme Coh construction uses the lin hmt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L369-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L369-L373

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

theorem GroundTheory.Arith.SchemeCoh.lin_hmt_zero (c : Chain ι 0) : lin (hmt (ι := ι) 0) c = 0 := by sorry
