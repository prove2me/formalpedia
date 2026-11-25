-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_summable_norm_iff_and_tsum_eq_coset2
-- name    : GroundTheory.Automorphic.Adele2.summable_norm_iff_and_tsum_eq_coset2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:55:57.947878+00:00
-- url     : https://prove2.me/theorems/3351c1cc-65b3-49b2-a9c4-24aa362c3128
-- title:
--   Adele2: summable norm iff and tsum eq coset2
-- statement:
--   The Adele2 construction uses the summable norm iff and tsum eq coset2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L362-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L362-L407

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

theorem GroundTheory.Automorphic.Adele2.summable_norm_iff_and_tsum_eq_coset2 (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : Fin 2 → K) (g : (Fin 2 → mixedSpace K) → ℂ) :
    (Summable (fun ξ => ‖(coset2 K I c).indicator (fun ξ => g (emb2 K ξ)) ξ‖) ↔
      Summable (fun α : idealLattice2 I => ‖g (α + emb2 K c)‖)) ∧
      ∑' ξ, (coset2 K I c).indicator (fun ξ => g (emb2 K ξ)) ξ =
        ∑' α : idealLattice2 I, g (α + emb2 K c) := by sorry
