-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_tsum_enorm_inner_self_le
-- name    : GroundTheory.Automorphic.tsum_enorm_inner_self_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:01.821749+00:00
-- url     : https://prove2.me/theorems/cc8da377-e178-41c6-b065-366e3e87ff87
-- title:
--   Automorphic: tsum enorm inner self le
-- statement:
--   The Automorphic construction uses the tsum enorm inner self le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L380-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceClass.lean#L380-L389

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem GroundTheory.Automorphic.tsum_enorm_inner_self_le {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    ∑' i, ‖⟪b i, T (b i)⟫_ℂ‖ₑ ≤ traceNorm T := by sorry
