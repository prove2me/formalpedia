-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_inv_p_le_cyclRadius
-- name    : GroundTheory.PAdicHodge.inv_p_le_cyclRadius
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:13.335305+00:00
-- url     : https://prove2.me/theorems/06db3804-2c7b-49ae-b18e-37fcd67d9967
-- title:
--   PAdic Hodge: inv p le cycl Radius
-- statement:
--   The PAdic Hodge construction uses the inv p le cycl Radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L218-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L218-L221

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

theorem GroundTheory.PAdicHodge.inv_p_le_cyclRadius (k : ℕ) : (p : ℝ)⁻¹ ≤ cyclRadius p (k + 1) := by sorry
