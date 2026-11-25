-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cycl_isPrimitiveRoot
-- name    : GroundTheory.PAdicHodge.normTrace_cycl_isPrimitiveRoot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:04.093219+00:00
-- url     : https://prove2.me/theorems/b173394c-acb3-4db8-a4dd-a3615e0ed44c
-- title:
--   PAdic Hodge: norm Trace cycl is Primitive Root
-- statement:
--   The PAdic Hodge construction uses the norm Trace cycl is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L164-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L164-L182

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.normTrace_cycl_isPrimitiveRoot {k : ℕ} (hk : 1 ≤ k) {η : PadicAlgCl p}
    (hη : IsPrimitiveRoot η (p ^ (k + 1))) : normTrace (cycl p k) η = 0 := by sorry
