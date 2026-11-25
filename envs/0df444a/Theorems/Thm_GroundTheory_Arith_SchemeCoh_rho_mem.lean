-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_rho_mem
-- name    : GroundTheory.Arith.SchemeCoh.rho_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:46.690449+00:00
-- url     : https://prove2.me/theorems/5504a0f5-8d70-4fa0-b667-d06802b6b53c
-- title:
--   Scheme Coh: rho mem
-- statement:
--   The Scheme Coh construction uses the rho mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L291-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L291-L300

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

theorem GroundTheory.Arith.SchemeCoh.rho_mem : ∀ (n : ℕ) (i : Fin (n + 1) → ι),
    rho n i ∈ Finsupp.supported ℤ ℤ (ordIn (Set.range i))
  := by sorry
