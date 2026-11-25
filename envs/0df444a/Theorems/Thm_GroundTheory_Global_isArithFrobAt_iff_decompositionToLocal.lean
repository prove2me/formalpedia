-- Prove2me | Theorems.Thm_GroundTheory_Global_isArithFrobAt_iff_decompositionToLocal
-- name    : GroundTheory.Global.isArithFrobAt_iff_decompositionToLocal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:01:45.181844+00:00
-- url     : https://prove2.me/theorems/6cfc2b39-9280-4cf8-b8f4-34d600ab7532
-- title:
--   Global: is Arith Frob At iff decomposition To Local
-- statement:
--   The Global construction uses the is Arith Frob At iff decomposition To Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L114-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L114-L150

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

theorem GroundTheory.Global.isArithFrobAt_iff_decompositionToLocal (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    IsArithFrobAt (𝓞 K) (σ : Gal(L/K)) w.asIdeal ↔
      ∀ x : 𝒪[w.adicCompletion L], integerAlgEquiv (v.adicCompletion K) (w.adicCompletion L)
        (decompositionToLocal v w σ) x - x ^ Nat.card 𝓀[v.adicCompletion K] ∈
          𝓂[w.adicCompletion L] := by sorry
