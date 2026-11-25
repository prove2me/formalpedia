-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_GaugeExists_natDegree_tmPoly_le
-- name    : GroundTheory.BlockD.FourierDecayAlt.GaugeExists.natDegree_tmPoly_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:12:15.136548+00:00
-- url     : https://prove2.me/theorems/df54418e-d5f8-5af7-8bcc-0fa5d604e660
-- title:
--   Gauge Exists: nat Degree tm Poly le
-- statement:
--   The Gauge Exists construction uses the nat Degree tm Poly le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/ConstantFrames/GaugeExistence/QdetSub.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/ConstantFrames/GaugeExistence/QdetSub.lean#L44-L50

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

theorem GroundTheory.BlockD.FourierDecayAlt.GaugeExists.natDegree_tmPoly_le {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    (tmPoly E k a b).natDegree ≤ if a = b then 1 else 0 := by sorry
