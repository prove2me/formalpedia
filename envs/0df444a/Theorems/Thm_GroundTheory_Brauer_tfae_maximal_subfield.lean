-- Prove2me | Theorems.Thm_GroundTheory_Brauer_tfae_maximal_subfield
-- name    : GroundTheory.Brauer.tfae_maximal_subfield
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:29:08.679656+00:00
-- url     : https://prove2.me/theorems/440ca309-7bcb-5d99-9655-2b30de8f70db
-- title:
--   Brauer: tfae maximal subfield
-- statement:
--   The Brauer construction uses the tfae maximal subfield property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L217-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L217-L226

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
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
open TensorProduct Module
universe u v w
variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]
variable [Algebra.IsCentral K D] [FiniteDimensional K D]

theorem GroundTheory.Brauer.tfae_maximal_subfield (F : Subalgebra K D) [IsMulCommutative F] :
    List.TFAE [Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F,
      Subalgebra.centralizer K (F : Set D) = F, finrank K F ^ 2 = finrank K D,
      finrank K F = degree K D] := by sorry
