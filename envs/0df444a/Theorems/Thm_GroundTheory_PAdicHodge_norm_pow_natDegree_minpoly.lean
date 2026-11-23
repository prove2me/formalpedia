-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_natDegree_minpoly
-- name    : GroundTheory.PAdicHodge.norm_pow_natDegree_minpoly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:49.013257+00:00
-- url     : https://prove2.me/theorems/0122fec6-c9bf-4da8-8404-9d61a68d6556
-- title:
--   PAdic Hodge: norm pow nat Degree minpoly
-- statement:
--   The PAdic Hodge construction uses the norm pow nat Degree minpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L66-L71

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

theorem GroundTheory.PAdicHodge.norm_pow_natDegree_minpoly (y : PadicAlgCl p) :
    ‖y‖ ^ (minpoly ℚ_[p] y).natDegree = ‖(minpoly ℚ_[p] y).coeff 0‖ := by sorry
