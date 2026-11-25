-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_GaugeExists_tmPoly_diag
-- name    : GroundTheory.BlockD.FourierDecayAlt.GaugeExists.tmPoly_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:00:15.676999+00:00
-- url     : https://prove2.me/theorems/50c184e7-fc28-489f-b343-50ddd8089112
-- title:
--   Gauge Exists: tm Poly diag
-- statement:
--   The Gauge Exists construction uses the tm Poly diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/ConstantFrames/GaugeExistence/QdetSub.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/ConstantFrames/GaugeExistence/QdetSub.lean#L104-L108

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

theorem GroundTheory.BlockD.FourierDecayAlt.GaugeExists.tmPoly_diag {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a : Fin n) :
    tmPoly E k a a = X + C (E a a - algebraMap ℂ A (k : ℂ)) := by sorry
