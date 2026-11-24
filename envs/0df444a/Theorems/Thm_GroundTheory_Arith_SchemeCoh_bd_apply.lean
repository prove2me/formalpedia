-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_apply
-- name    : GroundTheory.Arith.SchemeCoh.bd_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:26.329369+00:00
-- url     : https://prove2.me/theorems/0e3ff5c5-e950-4800-8fc7-e2da15629068
-- title:
--   Scheme Coh: bd apply
-- statement:
--   The Scheme Coh construction uses the bd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L34-L39

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

theorem GroundTheory.Arith.SchemeCoh.bd_apply (n : ℕ) (c : Chain ι (n + 1)) :
    bd n c = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • chainMap k.succAbove c := by sorry
