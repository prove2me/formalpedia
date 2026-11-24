-- Prove2me | Theorems.Thm_GroundTheory_Brauer_center_tensorProduct_eq_map_includeLeft
-- name    : GroundTheory.Brauer.center_tensorProduct_eq_map_includeLeft
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:19.119802+00:00
-- url     : https://prove2.me/theorems/1bcb6c68-0978-4723-963a-8fbb1681b6f0
-- title:
--   Brauer: center tensor Product eq map include Left
-- statement:
--   The Brauer construction uses the center tensor Product eq map include Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/TensorSimple.lean#L95-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/TensorSimple.lean#L95-L109

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
variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
variable (K A B)

theorem GroundTheory.Brauer.center_tensorProduct_eq_map_includeLeft [Algebra.IsCentral K A] :
    Subalgebra.center K (B ⊗[K] A) = (Subalgebra.center K B).map includeLeft := by sorry
