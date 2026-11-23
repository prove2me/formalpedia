-- Prove2me | Theorems.Thm_MutualCorrelatedAgreement_map_equiv
-- name    : MutualCorrelatedAgreement_map_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:26:01.300704+00:00
-- url     : https://prove2.me/theorems/a3b01ddf-4478-47ca-9024-0a2d08b63a9b
-- title:
--   Mutual Correlated Agreement map equiv: Mutual Correlated Agreement map equiv
-- statement:
--   Helper lemma: Mutual Correlated Agreement is preserved under domain equivalence
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L351-L378
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/State.lean#L351-L378

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [DecidableEq F]

theorem MutualCorrelatedAgreement_map_equiv [Fintype F] [DecidableEq F]
    [MeasurableSpace F] [DiscreteMeasurableSpace F]
    {L L' : Type*} [Fintype L] [Fintype L']
    (Gen : ProximityGenerator F)
    (C : Submodule F (L → F))
    (bound : ℝ) (errorstar : ℕ → ℝ → ℝ)
    (e : L' ≃ L)
    (h_mca : MutualCorrelatedAgreement Gen C bound errorstar) :
    MutualCorrelatedAgreement Gen (C.map (LinearEquiv.funCongrLeft F F e).toLinearMap) bound errorstar := by sorry
