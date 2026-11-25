-- Prove2me | Theorems.Thm_GroundTheory_Global_countable_quotient_of_isOpen
-- name    : GroundTheory.Global.countable_quotient_of_isOpen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:14:45.608434+00:00
-- url     : https://prove2.me/theorems/6286e064-da0c-547e-98e1-e361cec08ab6
-- title:
--   Global: countable quotient of is Open
-- statement:
--   The Global construction uses the countable quotient of is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureCosets.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureCosets.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
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
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.countable_quotient_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Countable (G ⧸ W) := by sorry
