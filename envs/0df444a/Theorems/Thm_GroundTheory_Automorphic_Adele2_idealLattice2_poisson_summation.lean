-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_idealLattice2_poisson_summation
-- name    : GroundTheory.Automorphic.Adele2.idealLattice2_poisson_summation
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:48:40.549037+00:00
-- url     : https://prove2.me/theorems/5c0fff35-16f9-4128-bbd2-130c60e6871b
-- title:
--   Adele2: ideal Lattice2 poisson summation
-- statement:
--   The Adele2 construction uses the ideal Lattice2 poisson summation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L299-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L299-L346

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

theorem GroundTheory.Automorphic.Adele2.idealLattice2_poisson_summation (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) (a : Fin 2 → mixedSpace K) :
    ∑' α : idealLattice2 I, f (α + a) =
      (∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ •
        ∑' β : idealLattice2 (fun i => traceDualIdeal K (I i)),
          mixedFourier2 K f β * 𝐞 (mixedPairing2 K β a) := by sorry
