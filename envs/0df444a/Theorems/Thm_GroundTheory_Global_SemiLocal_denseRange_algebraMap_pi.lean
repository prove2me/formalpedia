-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_denseRange_algebraMap_pi
-- name    : GroundTheory.Global.SemiLocal.denseRange_algebraMap_pi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:28.529284+00:00
-- url     : https://prove2.me/theorems/150ffecc-fd10-42d0-a004-75aaedfc8834
-- title:
--   Semi Local: dense Range algebra Map pi
-- statement:
--   The Semi Local construction uses the dense Range algebra Map pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Approximation.lean#L41-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Approximation.lean#L41-L85

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

theorem GroundTheory.Global.SemiLocal.denseRange_algebraMap_pi {ι : Type*} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (hw : Function.Injective w) :
    DenseRange (fun x : L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) x) := by sorry
