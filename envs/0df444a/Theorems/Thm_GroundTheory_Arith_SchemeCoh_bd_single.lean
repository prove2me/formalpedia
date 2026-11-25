-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_single
-- name    : GroundTheory.Arith.SchemeCoh.bd_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:21.227859+00:00
-- url     : https://prove2.me/theorems/d74478d3-8c77-4cc7-b696-c8a530e2515e
-- title:
--   Scheme Coh: bd single
-- statement:
--   The Scheme Coh construction uses the bd single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L41-L45

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

theorem GroundTheory.Arith.SchemeCoh.bd_single (n : ℕ) (i : Fin (n + 2) → ι) (z : ℤ) :
    bd n (Finsupp.single i z) =
      ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • Finsupp.single (i ∘ k.succAbove) z := by sorry
