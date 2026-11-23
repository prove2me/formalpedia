-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclRadius_le_one
-- name    : GroundTheory.PAdicHodge.cyclRadius_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:35.621399+00:00
-- url     : https://prove2.me/theorems/a0888e6c-6cd2-4db9-ae44-8a1f468ea93b
-- title:
--   PAdic Hodge: cycl Radius le one
-- statement:
--   The PAdic Hodge construction uses the cycl Radius le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L214-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/CyclotomicTower.lean#L214-L216

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

theorem GroundTheory.PAdicHodge.cyclRadius_le_one (j : ℕ) : cyclRadius p j ≤ 1 := by sorry
