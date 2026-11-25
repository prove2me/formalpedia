-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_inertia_iff_decompositionToLocal_mem
-- name    : GroundTheory.Global.mem_inertia_iff_decompositionToLocal_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:58.904488+00:00
-- url     : https://prove2.me/theorems/81b718e3-3032-4f1d-a5ad-9d430d3818ba
-- title:
--   Global: mem inertia iff decomposition To Local mem
-- statement:
--   The Global construction uses the mem inertia iff decomposition To Local mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L57-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Inertia.lean#L57-L89

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

theorem GroundTheory.Global.mem_inertia_iff_decompositionToLocal_mem (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    (σ : Gal(L/K)) ∈ w.asIdeal.inertia Gal(L/K) ↔
      decompositionToLocal v w σ ∈
        lowerRamificationGroup (v.adicCompletion K) (w.adicCompletion L) 0 := by sorry
