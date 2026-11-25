-- Prove2me | Theorems.Thm_GroundTheory_Global_finiteAdeleMeasure_integralFiniteAdeles
-- name    : GroundTheory.Global.finiteAdeleMeasure_integralFiniteAdeles
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:00:02.524196+00:00
-- url     : https://prove2.me/theorems/1a9d491b-9289-4aad-9a46-2c5b7cde0ecc
-- title:
--   Global: finite Adele Measure integral Finite Adeles
-- statement:
--   The Global construction uses the finite Adele Measure integral Finite Adeles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L61-L64

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
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
open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.finiteAdeleMeasure_integralFiniteAdeles :
    finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) = ((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) := by sorry
