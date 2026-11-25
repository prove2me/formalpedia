-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_dualLattice_euclidLattice2
-- name    : GroundTheory.Automorphic.Adele2.dualLattice_euclidLattice2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:35.163682+00:00
-- url     : https://prove2.me/theorems/662463a5-b86e-4b56-948a-8d51a33ebeb5
-- title:
--   Adele2: dual Lattice euclid Lattice2
-- statement:
--   The Adele2 construction uses the dual Lattice euclid Lattice2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L250-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L250-L283

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem GroundTheory.Automorphic.Adele2.dualLattice_euclidLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (euclidLattice2 I) = euclidConjLattice2 (fun i => traceDualIdeal K (I i)) := by sorry
