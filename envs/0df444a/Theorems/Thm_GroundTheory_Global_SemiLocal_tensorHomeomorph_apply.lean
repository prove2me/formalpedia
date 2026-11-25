-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
-- name    : GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:11:45.976805+00:00
-- url     : https://prove2.me/theorems/c6ff58ab-25b3-4cc1-beaf-cf1bfff38ecf
-- title:
--   Semi Local: tensor Homeomorph apply
-- statement:
--   The Semi Local construction uses the tensor Homeomorph apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Finite.lean#L142-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Finite.lean#L142-L144

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
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
open IsDedekindDomain NumberField TensorProduct Module
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.SemiLocal.tensorHomeomorph_apply [TopologicalSpace (v.adicCompletion K ⊗[K] L)]
    [IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)]
    (y : v.adicCompletion K ⊗[K] L) : tensorHomeomorph L v y = tensorEquiv L v y := by sorry

attribute [defeq] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
