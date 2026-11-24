-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_exists_sub_mem_pow_of_injective
-- name    : GroundTheory.Global.SemiLocal.exists_sub_mem_pow_of_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:23.457694+00:00
-- url     : https://prove2.me/theorems/ea6740ad-536c-4003-87bf-b3342f32ddef
-- title:
--   Semi Local: exists sub mem pow of injective
-- statement:
--   The Semi Local construction uses the exists sub mem pow of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Approximation.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Approximation.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
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
open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter
noncomputable section
open GroundTheory.Global.SemiLocal
variable {L : Type*} [Field L] [NumberField L]

theorem GroundTheory.Global.SemiLocal.exists_sub_mem_pow_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → HeightOneSpectrum (𝓞 L)) (hw : Function.Injective w) (i : ι) (n : ℕ) :
    ∃ a : 𝓞 L, ∀ j, a - (if j = i then 1 else 0) ∈ (w j).asIdeal ^ n := by sorry
