-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_eq_zpow_of_ne_zero
-- name    : GroundTheory.PAdicHodge.exists_norm_eq_zpow_of_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:43.645457+00:00
-- url     : https://prove2.me/theorems/c85566f4-6f47-4cde-9b46-cfa90c492677
-- title:
--   PAdic Hodge: exists norm eq zpow of ne zero
-- statement:
--   The PAdic Hodge construction uses the exists norm eq zpow of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L73-L74

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

theorem GroundTheory.PAdicHodge.exists_norm_eq_zpow_of_ne_zero {c : ℚ_[p]} (hc : c ≠ 0) : ∃ z : ℤ, ‖c‖ = (p : ℝ) ^ z := by sorry
