-- Prove2me | Theorems.Thm_GlobalTheory_HermClass_exists_short_of_trace_det
-- name    : GlobalTheory.HermClass.exists_short_of_trace_det
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:18:58.220703+00:00
-- url     : https://prove2.me/theorems/f67e9528-12dd-43ab-8fa2-05dae27f6497
-- title:
--   Herm Class: exists short of trace det
-- statement:
--   The Herm Class construction uses the exists short of trace det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsShortOfTraceDet.lean#L56-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsShortOfTraceDet.lean#L56-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MinkowskiLinearForms
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open MeasureTheory Module Submodule NumberField Matrix

theorem GlobalTheory.HermClass.exists_short_of_trace_det {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : LinearMap.BilinForm F V) (hq : LinearMap.IsSymm q) {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : κ → V) (hκ : Fintype.card κ = finrank ℚ F * finrank F V) {t : ℝ} (ht : 0 < t)
    (h0 : (Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det ≠ 0)
    (h1 : |(((Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det : ℚ) : ℝ)| <
      (t ^ Fintype.card κ) ^ 2) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ ∀ φ : F →+* ℂ,
      ‖φ (q (∑ i, z i • b i) (∑ i, z i • b i))‖ ≤ finrank F V * t ^ 2 := by sorry
