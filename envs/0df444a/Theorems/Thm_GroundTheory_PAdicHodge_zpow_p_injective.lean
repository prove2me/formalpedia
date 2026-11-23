-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_zpow_p_injective
-- name    : GroundTheory.PAdicHodge.zpow_p_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:08.693501+00:00
-- url     : https://prove2.me/theorems/b017ee5b-cd20-488d-bf60-e8cb0bc55fbc
-- title:
--   PAdic Hodge: zpow p injective
-- statement:
--   The PAdic Hodge construction uses the zpow p injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L78-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L78-L79

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

theorem GroundTheory.PAdicHodge.zpow_p_injective : Function.Injective fun z : ℤ => (p : ℝ) ^ z := by sorry
