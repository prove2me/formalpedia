-- Prove2me | Theorems.Thm_GroundTheory_Global_measurePreserving_mixedToEuclidean_symm
-- name    : GroundTheory.Global.measurePreserving_mixedToEuclidean_symm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:29.144403+00:00
-- url     : https://prove2.me/theorems/c1ec7f2d-1828-4767-9575-d7d4f54fb6b5
-- title:
--   Global: measure Preserving mixed To Euclidean symm
-- statement:
--   The Global construction uses the measure Preserving mixed To Euclidean symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticeEuclidean.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticeEuclidean.lean#L31-L35

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceDualLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean
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
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.measurePreserving_mixedToEuclidean_symm :
    MeasurePreserving (mixedToEuclidean K).symm volume (selfDualMeasure K) := by sorry
