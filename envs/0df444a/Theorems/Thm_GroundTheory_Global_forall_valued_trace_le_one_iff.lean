-- Prove2me | Theorems.Thm_GroundTheory_Global_forall_valued_trace_le_one_iff
-- name    : GroundTheory.Global.forall_valued_trace_le_one_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:16:11.900874+00:00
-- url     : https://prove2.me/theorems/a26db884-68d2-40c3-a54b-f6a22f3b9099
-- title:
--   Global: forall valued trace le one iff
-- statement:
--   The Global construction uses the forall valued trace le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L57-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L57-L78

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
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion M)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)]

theorem GroundTheory.Global.forall_valued_trace_le_one_iff (n : ℕ) :
    (∀ y : w.adicCompletion M, Valued.v y ≤ WithZero.exp (n : ℤ) →
      Valued.v (Algebra.trace (v.adicCompletion K) (w.adicCompletion M) y) ≤ 1) ↔
      n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M) := by sorry
