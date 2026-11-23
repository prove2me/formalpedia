-- Prove2me | Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- name    : GroundTheory.Brauer.tensorCSA_carrier
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:09.957933+00:00
-- url     : https://prove2.me/theorems/531f7f36-78a6-45ed-b5bd-d51b97dd5af5
-- title:
--   Brauer: tensor CSA carrier
-- statement:
--   The Brauer construction uses the tensor CSA carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/TensorSimple.lean#L236-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/TensorSimple.lean#L236-L236

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Algebra.TensorProduct
universe u v
variable {K : Type u} [Field K]

theorem GroundTheory.Brauer.tensorCSA_carrier (A B : CSA.{u, v} K) : (tensorCSA A B : Type v) = (A ⊗[K] B) := by sorry

attribute [defeq] GroundTheory.Brauer.tensorCSA_carrier
