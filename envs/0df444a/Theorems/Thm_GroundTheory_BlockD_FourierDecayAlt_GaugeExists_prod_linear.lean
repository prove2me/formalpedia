-- Prove2me | Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_GaugeExists_prod_linear
-- name    : GroundTheory.BlockD.FourierDecayAlt.GaugeExists.prod_linear
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:15:37.614933+00:00
-- url     : https://prove2.me/theorems/bf34679c-b608-4e0c-bc6d-910c8d2331c0
-- title:
--   Gauge Exists: prod linear
-- statement:
--   The Gauge Exists construction uses the prod linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/ConstantFrames/GaugeExistence/QdetSub.lean#L77-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/ConstantFrames/GaugeExistence/QdetSub.lean#L77-L102

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_QdetSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_prod

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
omit [Algebra ℂ A]

theorem GroundTheory.BlockD.FourierDecayAlt.GaugeExists.prod_linear (m : ℕ) (c : Fin m → A) :
    (List.ofFn fun k : Fin m => X + C (c k)).prod.natDegree ≤ m ∧
      (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff m = 1 ∧
      ∀ j, j + 1 = m → (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff j = ∑ k, c k := by sorry
