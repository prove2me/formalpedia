-- Prove2me | Theorems.Thm_GroundTheory_Global_idealLattice_summable_norm
-- name    : GroundTheory.Global.idealLattice_summable_norm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:55:47.206358+00:00
-- url     : https://prove2.me/theorems/bdda7e77-46cd-5604-80e4-e37b2332eeba
-- title:
--   Global: ideal Lattice summable norm
-- statement:
--   The Global construction uses the ideal Lattice summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticePoisson.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticePoisson.lean#L14-L16

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
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
open scoped Classical RealInnerProductSpace FourierTransform SchwartzMap nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.idealLattice_summable_norm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (f : 𝓢(mixedSpace K, ℂ))
    (a : mixedSpace K) : Summable fun α : idealLattice K I => ‖f (α + a)‖ := by sorry
