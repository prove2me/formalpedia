-- Prove2me | Theorems.Thm_GroundTheory_Global_infiniteAdeleMeasure_fundamentalSetInfinite
-- name    : GroundTheory.Global.infiniteAdeleMeasure_fundamentalSetInfinite
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:13:29.599331+00:00
-- url     : https://prove2.me/theorems/0593b01d-6ab2-4619-a176-2a9d92c1b1ce
-- title:
--   Global: infinite Adele Measure fundamental Set Infinite
-- statement:
--   The Global construction uses the infinite Adele Measure fundamental Set Infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L105-L111

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

theorem GroundTheory.Global.infiniteAdeleMeasure_fundamentalSetInfinite :
    infiniteAdeleMeasure K (fundamentalSetInfinite K) = (NNReal.sqrt ‖discr K‖₊ : ℝ≥0∞) := by sorry
