-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_analyticAt_of_differentiableOn_euclidean
-- name    : GlobalTheory.InjHol.analyticAt_of_differentiableOn_euclidean
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:30.100868+00:00
-- url     : https://prove2.me/theorems/09b95e3d-cc99-4506-981f-742ca87b775a
-- title:
--   Inj Hol: analytic At of differentiable On euclidean
-- statement:
--   The Inj Hol construction uses the analytic At of differentiable On euclidean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHolomorphicLocalInverseOfInjOn.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHolomorphicLocalInverseOfInjOn.lean#L9-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHolomorphicLocalInverseOfInjOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.InjHol

theorem GlobalTheory.InjHol.analyticAt_of_differentiableOn_euclidean {n : ℕ} {W : Set (V n)} {g : V n → V n} {a : V n}
    (hW : IsOpen W) (ha : a ∈ W) (hg : DifferentiableOn ℂ g W) : AnalyticAt ℂ g a := by sorry
