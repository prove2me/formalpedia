-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_dualIdealLattice2_summable_norm
-- name    : GroundTheory.Automorphic.Adele2.dualIdealLattice2_summable_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:29.000921+00:00
-- url     : https://prove2.me/theorems/cee8345e-f579-4cd6-91dd-b07893946778
-- title:
--   Adele2: dual Ideal Lattice2 summable norm
-- statement:
--   The Adele2 construction uses the dual Ideal Lattice2 summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L290-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L290-L297

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

theorem GroundTheory.Automorphic.Adele2.dualIdealLattice2_summable_norm (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) (a : Fin 2 → mixedSpace K) :
    Summable fun β : idealLattice2 (fun i => traceDualIdeal K (I i)) =>
      ‖mixedFourier2 K f β * 𝐞 (mixedPairing2 K β a)‖ := by sorry
