-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_smodEq_span_singleton_pow_iff
-- name    : GroundTheory.PAdicHodge.smodEq_span_singleton_pow_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:55.049313+00:00
-- url     : https://prove2.me/theorems/fbb753e4-7c34-44a5-8e34-3f258855392d
-- title:
--   PAdic Hodge: smod Eq span singleton pow iff
-- statement:
--   The PAdic Hodge construction uses the smod Eq span singleton pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerTheta.lean#L16-L19

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
variable {R : Type*} [CommRing R]

theorem GroundTheory.PAdicHodge.smodEq_span_singleton_pow_iff (a x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule R R)] ↔ a ^ n ∣ x - y := by sorry
