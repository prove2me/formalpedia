-- Prove2me | Theorems.Thm_GroundTheory_Global_decompositionMulEquiv_apply
-- name    : GroundTheory.Global.decompositionMulEquiv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:52:58.282832+00:00
-- url     : https://prove2.me/theorems/b14651c7-0e8e-4227-866d-fa2e9a398024
-- title:
--   Global: decomposition Mul Equiv apply
-- statement:
--   The Global construction uses the decomposition Mul Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Galois.lean#L269-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Galois.lean#L269-L271

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Degree
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem GroundTheory.Global.decompositionMulEquiv_apply (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    decompositionMulEquiv v w σ = decompositionToLocal v w σ := by sorry

attribute [defeq] GroundTheory.Global.decompositionMulEquiv_apply
