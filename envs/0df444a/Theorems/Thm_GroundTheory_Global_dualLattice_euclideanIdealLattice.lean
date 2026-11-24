-- Prove2me | Theorems.Thm_GroundTheory_Global_dualLattice_euclideanIdealLattice
-- name    : GroundTheory.Global.dualLattice_euclideanIdealLattice
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:48.87957+00:00
-- url     : https://prove2.me/theorems/1489abb3-42a7-415c-8473-35b1a14fbdc4
-- title:
--   Global: dual Lattice euclidean Ideal Lattice
-- statement:
--   The Global construction uses the dual Lattice euclidean Ideal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticeEuclidean.lean#L43-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticeEuclidean.lean#L43-L61

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

theorem GroundTheory.Global.dualLattice_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (euclideanIdealLattice K I) =
      euclideanConjIdealLattice K (traceDualIdeal K I) := by sorry
