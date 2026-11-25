-- Prove2me | Theorems.Thm_GroundTheory_Global_finiteSingleUnits_smul_eq_ker
-- name    : GroundTheory.Global.finiteSingleUnits_smul_eq_ker
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:13:44.44658+00:00
-- url     : https://prove2.me/theorems/036ef6ec-894c-40d2-90b0-3679e168a7e2
-- title:
--   Global: finite Single Units smul eq ker
-- statement:
--   The Global construction uses the finite Single Units smul eq ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L225-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L225-L244

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
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
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.finiteSingleUnits_smul_eq_ker {v : HeightOneSpectrum (𝓞 K)}
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) (hϖ0 : (ϖ : v.adicCompletion K) ≠ 0) :
    finiteSingleUnits v (Units.mk0 _ hϖ0) • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) =
      (((residueAt (K := K) v).ker.map (integralFiniteAdeles (𝓞 K) K).toAddSubgroup.subtype :
        AddSubgroup 𝔸ᶠ[K]) : Set 𝔸ᶠ[K]) := by sorry
