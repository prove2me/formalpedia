-- Prove2me | Theorems.Thm_GroundTheory_Global_inner_mixedToEuclideanConj_mixedToEuclidean
-- name    : GroundTheory.Global.inner_mixedToEuclideanConj_mixedToEuclidean
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:22.594803+00:00
-- url     : https://prove2.me/theorems/8fb69a1f-c998-4a2c-94ab-c332f3cc006b
-- title:
--   Global: inner mixed To Euclidean Conj mixed To Euclidean
-- statement:
--   The Global construction uses the inner mixed To Euclidean Conj mixed To Euclidean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticeEuclidean.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticeEuclidean.lean#L63-L65

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

theorem GroundTheory.Global.inner_mixedToEuclideanConj_mixedToEuclidean (β a : mixedSpace K) :
    ⟪mixedToEuclideanConj K β, mixedToEuclidean K a⟫ = mixedTraceForm K β a := by sorry
