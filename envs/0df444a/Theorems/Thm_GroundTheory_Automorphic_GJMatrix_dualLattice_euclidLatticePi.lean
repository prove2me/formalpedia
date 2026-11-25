-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_dualLattice_euclidLatticePi
-- name    : GroundTheory.Automorphic.GJMatrix.dualLattice_euclidLatticePi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:48.418843+00:00
-- url     : https://prove2.me/theorems/ac5ade0a-60c2-4119-a814-1b11e5ca9a91
-- title:
--   GJMatrix: dual Lattice euclid Lattice Pi
-- statement:
--   The GJMatrix construction uses the dual Lattice euclid Lattice Pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L277-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L277-L310

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
variable {K}

theorem GroundTheory.Automorphic.GJMatrix.dualLattice_euclidLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (euclidLatticePi I) = euclidConjLatticePi (fun i ↦ traceDualIdeal K (I i)) := by sorry
