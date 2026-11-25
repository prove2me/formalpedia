-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_dualIdealLatticePi_summable_norm
-- name    : GroundTheory.Automorphic.GJMatrix.dualIdealLatticePi_summable_norm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:56:22.844321+00:00
-- url     : https://prove2.me/theorems/c90e8dd6-998b-419d-95fa-f707047db336
-- title:
--   GJMatrix: dual Ideal Lattice Pi summable norm
-- statement:
--   The GJMatrix construction uses the dual Ideal Lattice Pi summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L317-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L317-L324

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

theorem GroundTheory.Automorphic.GJMatrix.dualIdealLatticePi_summable_norm (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(ι → mixedSpace K, ℂ)) (a : ι → mixedSpace K) :
    Summable fun β : idealLatticePi (fun i ↦ traceDualIdeal K (I i)) ↦
      ‖mixedFourierPi K f β * 𝐞 (mixedPairingPi K β a)‖ := by sorry
