-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_norm_pi
-- name    : GroundTheory.Global.SemiLocal.norm_pi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:28.864994+00:00
-- url     : https://prove2.me/theorems/06ad1ded-6852-4dd7-9d66-94d8e61af7ba
-- title:
--   Semi Local: norm pi
-- statement:
--   The Semi Local construction uses the norm pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean#L42-L46

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Matrix
noncomputable section
open GroundTheory.Global.SemiLocal
variable {R : Type*} [Field R] {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)] [∀ i, Module.Finite R (S i)]

theorem GroundTheory.Global.SemiLocal.norm_pi (x : ∀ i, S i) : Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by sorry
