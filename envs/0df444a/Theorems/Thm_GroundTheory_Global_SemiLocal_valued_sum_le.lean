-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_valued_sum_le
-- name    : GroundTheory.Global.SemiLocal.valued_sum_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:17.758905+00:00
-- url     : https://prove2.me/theorems/e03bd1a1-b8d3-4864-b1a1-85a90c0e5115
-- title:
--   Semi Local: valued sum le
-- statement:
--   The Semi Local construction uses the valued sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L91-L100

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
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
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
variable {ι : Type*} [Fintype ι]

theorem GroundTheory.Global.SemiLocal.valued_sum_le (ω : ι → 𝓞 L) (c : ι → v.adicCompletion K) (M : ℤᵐ⁰)
    (hM : ∀ j, Valued.v (c j) ≤ M) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) ≤ M ^ w.asIdeal.ramificationIdx (𝓞 K) := by sorry
