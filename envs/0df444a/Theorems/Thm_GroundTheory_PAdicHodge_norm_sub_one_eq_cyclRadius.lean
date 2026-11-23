-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_eq_cyclRadius
-- name    : GroundTheory.PAdicHodge.norm_sub_one_eq_cyclRadius
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:47.868985+00:00
-- url     : https://prove2.me/theorems/d54607f9-b86b-4c54-b5f2-5dbe69525f8e
-- title:
--   PAdic Hodge: norm sub one eq cycl Radius
-- statement:
--   The PAdic Hodge construction uses the norm sub one eq cycl Radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L202-L205

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

theorem GroundTheory.PAdicHodge.norm_sub_one_eq_cyclRadius {η : PadicAlgCl p} {j : ℕ} (hη : IsPrimitiveRoot η (p ^ j)) :
    ‖η - 1‖ = cyclRadius p j := by sorry
