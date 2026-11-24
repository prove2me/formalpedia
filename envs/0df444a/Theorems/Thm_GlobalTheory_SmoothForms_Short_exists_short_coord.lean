-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_Short_exists_short_coord
-- name    : GlobalTheory.SmoothForms.Short.exists_short_coord
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:20.261881+00:00
-- url     : https://prove2.me/theorems/46552ea2-8080-4832-9e79-d52b4073b51a
-- title:
--   Short: exists short coord
-- statement:
--   The Short construction uses the exists short coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean#L29-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean#L29-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms GlobalTheory.HermClass Module Submodule NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Short

theorem GlobalTheory.SmoothForms.Short.exists_short_coord {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {V : Type} [AddCommGroup V] [Module F V] {ι : Type} [Fintype ι] (e : Basis ι F V)
    (q : LinearMap.BilinForm F V) (he : ∀ k l, l ≠ k → q (e l) (e k) = 0) {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : κ → V) (hκ : Fintype.card κ = finrank ℚ F * Fintype.card ι) {t : ℝ} (ht : 0 < t)
    (h0 : (Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det ≠ 0)
    (h1 : |(((Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det : ℚ) : ℝ)| <
      (t ^ Fintype.card κ) ^ 2) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ ∀ φ : F →+* ℂ,
      ‖φ (q (∑ i, z i • b i) (∑ i, z i • b i))‖ ≤ Fintype.card ι * t ^ 2 ∧
      ∀ k, ‖φ (e.repr (∑ i, z i • b i) k)‖ ^ 2 * ‖φ (q (e k) (e k))‖ ≤ t ^ 2 := by sorry
