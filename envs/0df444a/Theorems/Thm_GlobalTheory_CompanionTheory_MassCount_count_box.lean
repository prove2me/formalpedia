-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MassCount_count_box
-- name    : GlobalTheory.CompanionTheory.MassCount.count_box
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:53:07.585651+00:00
-- url     : https://prove2.me/theorems/ec496a43-52ad-4593-b466-fff632e30c01
-- title:
--   Mass Count: count box
-- statement:
--   The Mass Count construction uses the count box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormThetaMul.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormThetaMul.lean#L16-L20

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GaloisBoundSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormThetaMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MassCount
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.MassCount.count_box [IsTotallyReal F] (N : ℕ) (hN : 0 < N) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (B : ℝ) (hB : 0 ≤ B) :
    {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.Finite ∧
    (({x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = N * x) ∧ ∀ w : InfinitePlace F, w x ≤ B}.ncard : ℕ) : ℝ) *
      (Ideal.absNorm I : ℝ) ≤ (4 * B * N) ^ Module.finrank ℚ F := by sorry
