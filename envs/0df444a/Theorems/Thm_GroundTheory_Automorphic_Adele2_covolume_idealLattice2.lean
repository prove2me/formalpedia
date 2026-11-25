-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_covolume_idealLattice2
-- name    : GroundTheory.Automorphic.Adele2.covolume_idealLattice2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:48:05.96362+00:00
-- url     : https://prove2.me/theorems/bf597efd-9c03-41d6-bfe2-ae2a44c1e4b8
-- title:
--   Adele2: covolume ideal Lattice2
-- statement:
--   The Adele2 construction uses the covolume ideal Lattice2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L213-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L213-L221

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

theorem GroundTheory.Automorphic.Adele2.covolume_idealLattice2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (idealLattice2 I) (mixedMeasure2 K) =
      ∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|) := by sorry
