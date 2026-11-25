-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_isAddFundamentalDomain_idealLatticePi
-- name    : GroundTheory.Automorphic.GJMatrix.isAddFundamentalDomain_idealLatticePi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:56:37.932303+00:00
-- url     : https://prove2.me/theorems/3b733711-bbee-475b-a518-6162aaca5149
-- title:
--   GJMatrix: is Add Fundamental Domain ideal Lattice Pi
-- statement:
--   The GJMatrix construction uses the is Add Fundamental Domain ideal Lattice Pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L214-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L214-L242

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

theorem GroundTheory.Automorphic.GJMatrix.isAddFundamentalDomain_idealLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsAddFundamentalDomain (idealLatticePi I)
      (Set.univ.pi fun i ↦ ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis ℝ
          (idealLattice K (I i)))) (mixedMeasurePi K) := by sorry
