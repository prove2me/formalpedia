-- Prove2me | Theorems.Thm_GroundTheory_Global_eq_prod_map_fst_restrict
-- name    : GroundTheory.Global.eq_prod_map_fst_restrict
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:42.233682+00:00
-- url     : https://prove2.me/theorems/85273978-9e7d-5b85-8ae9-12200fb6bbb4
-- title:
--   Global: eq prod map fst restrict
-- statement:
--   The Global construction uses the eq prod map fst restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureNormOne.lean#L264-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureNormOne.lean#L264-L268

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace Real
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] [LocallyCompactSpace H] [SecondCountableTopology H]

theorem GroundTheory.Global.eq_prod_map_fst_restrict (lam : Measure (G × H)) [lam.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] {S : Set H} (hν : ν S = 1) :
    lam = (Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ S))).prod ν := by sorry
