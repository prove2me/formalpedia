-- Prove2me | Theorems.Thm_GroundTheory_Global_integerAlgEquiv_mem_maximalIdeal_iff
-- name    : GroundTheory.Global.integerAlgEquiv_mem_maximalIdeal_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:25.856482+00:00
-- url     : https://prove2.me/theorems/d3ae85f5-5ab6-4cbb-bb5d-ce23d2db7460
-- title:
--   Global: integer Alg Equiv mem maximal Ideal iff
-- statement:
--   The Global construction uses the integer Alg Equiv mem maximal Ideal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L51-L55

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Inertia
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem GroundTheory.Global.integerAlgEquiv_mem_maximalIdeal_iff (τ : Gal(w.adicCompletion L/v.adicCompletion K))
    (x : 𝒪[w.adicCompletion L]) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L) τ x ∈ 𝓂[w.adicCompletion L] ↔
      x ∈ 𝓂[w.adicCompletion L] := by sorry
