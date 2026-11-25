-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_ocone_zero
-- name    : GroundTheory.Arith.SchemeCoh.bd_ocone_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:53.10147+00:00
-- url     : https://prove2.me/theorems/a8425eb9-dd7f-450e-b561-55d3dfe36e8a
-- title:
--   Scheme Coh: bd ocone zero
-- statement:
--   The Scheme Coh construction uses the bd ocone zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L224-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L224-L243

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

theorem GroundTheory.Arith.SchemeCoh.bd_ocone_zero (s : ι) {c : Chain ι 0} (hc : c ∈ Finsupp.supported ℤ ℤ (ordFrom s)) :
    bd 0 (ocone s c) = c - aug c • Finsupp.single (fun _ => s) 1 := by sorry
