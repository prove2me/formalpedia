-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_norm_algebraMap_le_of_mem_pow
-- name    : GroundTheory.Global.SemiLocal.norm_algebraMap_le_of_mem_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:31.764767+00:00
-- url     : https://prove2.me/theorems/c62c3753-7e72-4c1c-9b5b-f6e1ae6297cf
-- title:
--   Semi Local: norm algebra Map le of mem pow
-- statement:
--   The Semi Local construction uses the norm algebra Map le of mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Approximation.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Approximation.lean#L22-L32

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

theorem GroundTheory.Global.SemiLocal.norm_algebraMap_le_of_mem_pow (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (n : ℕ)
    (ha : a ∈ w.asIdeal ^ n) :
    ‖algebraMap (𝓞 L) (w.adicCompletion L) a‖ ≤
      ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) ^ n := by sorry
