-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_euclideanIdealLattice
-- name    : GroundTheory.Global.mem_euclideanIdealLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:03.542808+00:00
-- url     : https://prove2.me/theorems/d1842f9e-76a3-4232-b848-372903181b1b
-- title:
--   Global: mem euclidean Ideal Lattice
-- statement:
--   The Global construction uses the mem euclidean Ideal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticeEuclidean.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticeEuclidean.lean#L22-L24

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

theorem GroundTheory.Global.mem_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : euclidean.mixedSpace K) :
    u ∈ euclideanIdealLattice K I ↔ (mixedToEuclidean K).symm u ∈ idealLattice K I := by sorry
