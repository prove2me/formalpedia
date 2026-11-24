-- Prove2me | Theorems.Thm_GlobalTheory_Phase_GaussSum_quat_form
-- name    : GlobalTheory.Phase.GaussSum.quat_form
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:41.609473+00:00
-- url     : https://prove2.me/theorems/ea107a78-dfcb-4221-80e6-3791cc4f6eee
-- title:
--   Gauss Sum: quat form
-- statement:
--   The Gauss Sum construction uses the quat form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSum.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSum.lean#L66-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.GaussSum

theorem GlobalTheory.Phase.GaussSum.quat_form {M W : Type} [AddCommGroup M] [AddCommGroup W] (β : M →+ M →+ W) (a b c d : ℤ)
    (x y : Fin 4 → M) :
    ∑ i, β (quat a b c d x i) (quat a b c d y i) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • ∑ i, β (x i) (y i) := by sorry
