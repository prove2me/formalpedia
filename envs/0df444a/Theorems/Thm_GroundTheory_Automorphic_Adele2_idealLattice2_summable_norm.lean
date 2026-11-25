-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_idealLattice2_summable_norm
-- name    : GroundTheory.Automorphic.Adele2.idealLattice2_summable_norm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:48:43.917214+00:00
-- url     : https://prove2.me/theorems/351f9467-ecf7-4b65-a4c6-22ff42802124
-- title:
--   Adele2: ideal Lattice2 summable norm
-- statement:
--   The Adele2 construction uses the ideal Lattice2 summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L285-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L285-L288

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

theorem GroundTheory.Automorphic.Adele2.idealLattice2_summable_norm (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) (a : Fin 2 → mixedSpace K) :
    Summable fun α : idealLattice2 I => ‖f (α + a)‖ := by sorry
