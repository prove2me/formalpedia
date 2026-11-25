-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_isAddFundamentalDomain_idealLattice2
-- name    : GroundTheory.Automorphic.Adele2.isAddFundamentalDomain_idealLattice2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:48:19.096505+00:00
-- url     : https://prove2.me/theorems/f3089812-5b30-4776-b4c8-f62c3cb2f6ac
-- title:
--   Adele2: is Add Fundamental Domain ideal Lattice2
-- statement:
--   The Adele2 construction uses the is Add Fundamental Domain ideal Lattice2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L183-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L183-L211

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

theorem GroundTheory.Automorphic.Adele2.isAddFundamentalDomain_idealLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsAddFundamentalDomain (idealLattice2 I)
      (Set.univ.pi fun i => ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis ℝ
          (idealLattice K (I i)))) (mixedMeasure2 K) := by sorry
