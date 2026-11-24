-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_isUnit_of_isUnit_coeff_zero
-- name    : GroundTheory.PAdicHodge.isUnit_of_isUnit_coeff_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:49.239585+00:00
-- url     : https://prove2.me/theorems/9f72927d-d910-4ada-81e4-dec844a1d542
-- title:
--   PAdic Hodge: is Unit of is Unit coeff zero
-- statement:
--   The PAdic Hodge construction uses the is Unit of is Unit coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L58-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L58-L68

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] [CharP A p] [PerfectRing A p]

theorem GroundTheory.PAdicHodge.isUnit_of_isUnit_coeff_zero {v : WittVector p A} (h : IsUnit (v.coeff 0)) : IsUnit v := by sorry
