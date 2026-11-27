-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_poissonPi_coset
-- name    : GroundTheory.Automorphic.GJMatrix.poissonPi_coset
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:57:08.390396+00:00
-- url     : https://prove2.me/theorems/66343e8d-baaa-5132-a7d5-a06db7ca22b8
-- title:
--   GJMatrix: poisson Pi coset
-- statement:
--   The GJMatrix construction uses the poisson Pi coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L434-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L434-L452

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

theorem GroundTheory.Automorphic.GJMatrix.poissonPi_coset (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ι → K)
    (f : 𝓢(ι → mixedSpace K, ℂ)) :
    Summable (fun ξ : ι → K ↦ ‖(cosetPi K I c).indicator (fun ξ ↦ f (embPi K ξ)) ξ‖) ∧
    Summable (fun η : ι → K ↦ ‖(cosetPi K (fun i ↦ traceDualIdeal K (I i)) 0).indicator
      (fun η ↦ mixedFourierPi K f (embPi K η) *
        (𝐞 (mixedPairingPi K (embPi K η) (embPi K c)) : ℂ)) η‖) ∧
    ∑' ξ : ι → K, (cosetPi K I c).indicator (fun ξ ↦ f (embPi K ξ)) ξ =
      (((∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ : ℝ) : ℂ) *
        ∑' η : ι → K, (cosetPi K (fun i ↦ traceDualIdeal K (I i)) 0).indicator
          (fun η ↦ mixedFourierPi K f (embPi K η) *
            (𝐞 (mixedPairingPi K (embPi K η) (embPi K c)) : ℂ)) η := by sorry
