-- Prove2me | Theorems.Thm_GroundTheory_Brauer_SkolemNoether_bimoduleHom_tmul
-- name    : GroundTheory.Brauer.SkolemNoether.bimoduleHom_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:19.272502+00:00
-- url     : https://prove2.me/theorems/c7439323-e1fc-4d6a-92b6-f39e98e9189c
-- title:
--   Skolem Noether: bimodule Hom tmul
-- statement:
--   The Skolem Noether construction uses the bimodule Hom tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L59-L61

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
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
open TensorProduct
open GroundTheory.Brauer.SkolemNoether
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

theorem GroundTheory.Brauer.SkolemNoether.bimoduleHom_tmul (f : B →ₐ[K] A) (a : A) (b : Bᵐᵒᵖ) (x : A) :
    bimoduleHom f (a ⊗ₜ[K] b) x = a * x * f b.unop := by sorry
