-- Prove2me | Theorems.Thm_GroundTheory_Global_decompositionToLocal_arithFrobAt
-- name    : GroundTheory.Global.decompositionToLocal_arithFrobAt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:24.586243+00:00
-- url     : https://prove2.me/theorems/9bf48616-a0ff-44dc-b69d-c871d270141d
-- title:
--   Global: decomposition To Local arith Frob At
-- statement:
--   The Global construction uses the decomposition To Local arith Frob At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L152-L156

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
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem GroundTheory.Global.decompositionToLocal_arithFrobAt (x : 𝒪[w.adicCompletion L]) :
    integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w (arithFrobAtDecomposition w)) x -
      x ^ Nat.card 𝓀[v.adicCompletion K] ∈ 𝓂[w.adicCompletion L] := by sorry
