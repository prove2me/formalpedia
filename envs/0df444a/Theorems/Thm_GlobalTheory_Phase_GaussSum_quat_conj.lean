-- Prove2me | Theorems.Thm_GlobalTheory_Phase_GaussSum_quat_conj
-- name    : GlobalTheory.Phase.GaussSum.quat_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:44:03.469308+00:00
-- url     : https://prove2.me/theorems/553f06bc-3c00-4fb3-bdae-c0186a720a7f
-- title:
--   Gauss Sum: quat conj
-- statement:
--   The Gauss Sum construction uses the quat conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSum.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSum.lean#L62-L64

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

theorem GlobalTheory.Phase.GaussSum.quat_conj {M : Type} [AddCommGroup M] (a b c d : ℤ) (x : Fin 4 → M) (i : Fin 4) :
    quat a (-b) (-c) (-d) (quat a b c d x) i = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • x i := by sorry
