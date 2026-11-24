-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_aug_bd
-- name    : GroundTheory.Arith.SchemeCoh.aug_bd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:10.447198+00:00
-- url     : https://prove2.me/theorems/599f65d2-9af1-4c6d-be60-419a356650d6
-- title:
--   Scheme Coh: aug bd
-- statement:
--   The Scheme Coh construction uses the aug bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L56-L62

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

theorem GroundTheory.Arith.SchemeCoh.aug_bd (c : Chain ι 1) : aug (bd 0 c) = 0 := by sorry
