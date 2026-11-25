-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_valued_sum_eq_one
-- name    : GroundTheory.Global.SemiLocal.valued_sum_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:22.600269+00:00
-- url     : https://prove2.me/theorems/ec44706e-7141-4550-8b55-80f7f5b70f73
-- title:
--   Semi Local: valued sum eq one
-- statement:
--   The Semi Local construction uses the valued sum eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L102-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L102-L146

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

theorem GroundTheory.Global.SemiLocal.valued_sum_eq_one (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (d : ι → v.adicCompletion K) (hd : ∀ j, Valued.v (d j) ≤ 1) (j0 : ι)
    (hj0 : Valued.v (d j0) = 1) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (d j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) = 1 := by sorry
