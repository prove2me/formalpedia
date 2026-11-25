-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_natDegree_minpoly_cycl_of_adjoin_eq
-- name    : GroundTheory.PAdicHodge.natDegree_minpoly_cycl_of_adjoin_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:26.52006+00:00
-- url     : https://prove2.me/theorems/2d964877-407f-424e-ac7e-e127afbe8df9
-- title:
--   PAdic Hodge: nat Degree minpoly cycl of adjoin eq
-- statement:
--   The PAdic Hodge construction uses the nat Degree minpoly cycl of adjoin eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L153-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L153-L162

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

theorem GroundTheory.PAdicHodge.natDegree_minpoly_cycl_of_adjoin_eq {k : ℕ} (hk : 1 ≤ k) {y : PadicAlgCl p}
    (hy : ℚ_[p]⟮y⟯ = cycl p (k + 1)) : (minpoly (cycl p k) y).natDegree = p := by sorry
