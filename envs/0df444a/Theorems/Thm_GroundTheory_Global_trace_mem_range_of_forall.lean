-- Prove2me | Theorems.Thm_GroundTheory_Global_trace_mem_range_of_forall
-- name    : GroundTheory.Global.trace_mem_range_of_forall
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:35.823915+00:00
-- url     : https://prove2.me/theorems/3ee4f857-11c4-4bfe-b45e-4929be7eec79
-- title:
--   Global: trace mem range of forall
-- statement:
--   The Global construction uses the trace mem range of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L194-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L194-L201

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
open SemiLocal
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem GroundTheory.Global.trace_mem_range_of_forall (x : M)
    (h : ∀ (v : HeightOneSpectrum (𝓞 K)) (u : PlacesOver M v),
      Valued.v (Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
        (algebraMap M (u.1.adicCompletion M) x)) ≤ 1) :
    Algebra.trace K M x ∈ (algebraMap (𝓞 K) K).range := by sorry
