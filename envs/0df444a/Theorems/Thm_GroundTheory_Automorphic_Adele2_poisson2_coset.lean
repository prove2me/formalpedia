-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_poisson2_coset
-- name    : GroundTheory.Automorphic.Adele2.poisson2_coset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:02.283912+00:00
-- url     : https://prove2.me/theorems/6c41d545-e771-5230-89e7-7e232e615cdb
-- title:
--   Adele2: poisson2 coset
-- statement:
--   The Adele2 construction uses the poisson2 coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L409-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L409-L427

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

theorem GroundTheory.Automorphic.Adele2.poisson2_coset (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : Fin 2 → K)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) :
    Summable (fun ξ : Fin 2 → K => ‖(coset2 K I c).indicator (fun ξ => f (emb2 K ξ)) ξ‖) ∧
    Summable (fun η : Fin 2 → K => ‖(coset2 K (fun i => traceDualIdeal K (I i)) 0).indicator
      (fun η => mixedFourier2 K f (emb2 K η) *
        (𝐞 (mixedPairing2 K (emb2 K η) (emb2 K c)) : ℂ)) η‖) ∧
    ∑' ξ : Fin 2 → K, (coset2 K I c).indicator (fun ξ => f (emb2 K ξ)) ξ =
      (((∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ : ℝ) : ℂ) *
        ∑' η : Fin 2 → K, (coset2 K (fun i => traceDualIdeal K (I i)) 0).indicator
          (fun η => mixedFourier2 K f (emb2 K η) *
            (𝐞 (mixedPairing2 K (emb2 K η) (emb2 K c)) : ℂ)) η := by sorry
