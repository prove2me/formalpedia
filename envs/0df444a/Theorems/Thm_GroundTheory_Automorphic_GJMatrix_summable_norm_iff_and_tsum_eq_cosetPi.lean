-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_summable_norm_iff_and_tsum_eq_cosetPi
-- name    : GroundTheory.Automorphic.GJMatrix.summable_norm_iff_and_tsum_eq_cosetPi
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:55:52.935304+00:00
-- url     : https://prove2.me/theorems/c49c1040-0482-4f12-a690-046daf2ff9ec
-- title:
--   GJMatrix: summable norm iff and tsum eq coset Pi
-- statement:
--   The GJMatrix construction uses the summable norm iff and tsum eq coset Pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L387-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L387-L432

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
omit [Fintype ι]

theorem GroundTheory.Automorphic.GJMatrix.summable_norm_iff_and_tsum_eq_cosetPi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : ι → K) (g : (ι → mixedSpace K) → ℂ) :
    (Summable (fun ξ ↦ ‖(cosetPi K I c).indicator (fun ξ ↦ g (embPi K ξ)) ξ‖) ↔
      Summable (fun α : idealLatticePi I ↦ ‖g (α + embPi K c)‖)) ∧
      ∑' ξ, (cosetPi K I c).indicator (fun ξ ↦ g (embPi K ξ)) ξ =
        ∑' α : idealLatticePi I, g (α + embPi K c) := by sorry
