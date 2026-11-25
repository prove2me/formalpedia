-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_GaugeExists_evU_tmPoly
-- name    : GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_tmPoly
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:11:44.470429+00:00
-- url     : https://prove2.me/theorems/4b0bd39d-d860-516e-b2ec-f91ef3f8b586
-- title:
--   Gauge Exists: ev U tm Poly
-- statement:
--   The Gauge Exists construction uses the ev U tm Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/ConstantFrames/GaugeExistence/QdetSub.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/ConstantFrames/GaugeExistence/QdetSub.lean#L27-L30

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_QdetSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial Formalism.REAL
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.GaugeExists
noncomputable section
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_tmPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (k : ℕ) (a b : Fin n) :
    evU u (tmPoly E k a b) = Tm E (u - (k : ℂ)) a b := by sorry
