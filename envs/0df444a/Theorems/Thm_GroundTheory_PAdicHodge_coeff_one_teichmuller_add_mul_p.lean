-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_coeff_one_teichmuller_add_mul_p
-- name    : GroundTheory.PAdicHodge.coeff_one_teichmuller_add_mul_p
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:47.31996+00:00
-- url     : https://prove2.me/theorems/da097701-b45f-477c-a9bb-45f0ca357647
-- title:
--   PAdic Hodge: coeff one teichmuller add mul p
-- statement:
--   The PAdic Hodge construction uses the coeff one teichmuller add mul p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L50-L56

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
omit [PerfectRing A p]

theorem GroundTheory.PAdicHodge.coeff_one_teichmuller_add_mul_p (c : A) (v : WittVector p A) :
    (teichmuller p c + v * p).coeff 1 = v.coeff 0 ^ p := by sorry
