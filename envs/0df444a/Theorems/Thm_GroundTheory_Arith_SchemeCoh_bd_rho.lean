-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_rho
-- name    : GroundTheory.Arith.SchemeCoh.bd_rho
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:39.221978+00:00
-- url     : https://prove2.me/theorems/d60e4b65-bfee-4786-ade7-e2fe6ff07187
-- title:
--   Scheme Coh: bd rho
-- statement:
--   The Scheme Coh construction uses the bd rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L302-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L302-L338

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

theorem GroundTheory.Arith.SchemeCoh.bd_rho : ∀ (n : ℕ) (i : Fin (n + 2) → ι),
    bd n (rho (n + 1) i) = lin (rho n) (bd n (Finsupp.single i 1))
  := by sorry
