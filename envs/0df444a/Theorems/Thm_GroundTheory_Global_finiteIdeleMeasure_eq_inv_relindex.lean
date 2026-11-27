-- Prove2me | Theorems.Thm_GroundTheory_Global_finiteIdeleMeasure_eq_inv_relindex
-- name    : GroundTheory.Global.finiteIdeleMeasure_eq_inv_relindex
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:56:56.775214+00:00
-- url     : https://prove2.me/theorems/28621c82-50c9-5d3f-8aac-60fb7fd07c6f
-- title:
--   Global: finite Idele Measure eq inv relindex
-- statement:
--   The Global construction uses the finite Idele Measure eq inv relindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureQuotient.lean#L322-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureQuotient.lean#L322-L362

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.finiteIdeleMeasure_eq_inv_relindex (W : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hWo : IsOpen (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ)) (hW : W ≤ finiteIntegralUnits K) :
    finiteIdeleMeasure K W = ((W.relIndex (finiteIntegralUnits K) : ℕ) : ℝ≥0∞)⁻¹ := by sorry
