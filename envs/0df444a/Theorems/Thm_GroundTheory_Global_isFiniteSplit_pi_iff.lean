-- Prove2me | Theorems.Thm_GroundTheory_Global_isFiniteSplit_pi_iff
-- name    : GroundTheory.Global.isFiniteSplit_pi_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:46:18.965936+00:00
-- url     : https://prove2.me/theorems/a246bd24-df44-4319-9ef3-ffd08904aefa
-- title:
--   Global: is Finite Split pi iff
-- statement:
--   The Global construction uses the is Finite Split pi iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean#L37-L46

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module
open scoped TensorProduct
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem GroundTheory.Global.isFiniteSplit_pi_iff {ι : Type*} [Finite ι] {E : ι → Type*} [∀ i, Field (E i)]
    [∀ i, Algebra F (E i)] :
    Algebra.IsFiniteSplit F (∀ i, E i) ↔ ∀ i, finrank F (E i) = 1 := by sorry
