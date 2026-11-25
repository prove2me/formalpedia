-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_toNNReal_exp_neg_one_lt_one
-- name    : GroundTheory.Global.SemiLocal.toNNReal_exp_neg_one_lt_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:17.958388+00:00
-- url     : https://prove2.me/theorems/a1f7f4f9-683e-4463-af95-258df5e4f2eb
-- title:
--   Semi Local: to NNReal exp neg one lt one
-- statement:
--   The Semi Local construction uses the to NNReal exp neg one lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Approximation.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Approximation.lean#L34-L39

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

theorem GroundTheory.Global.SemiLocal.toNNReal_exp_neg_one_lt_one (w : HeightOneSpectrum (𝓞 L)) :
    ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) < 1 := by sorry
