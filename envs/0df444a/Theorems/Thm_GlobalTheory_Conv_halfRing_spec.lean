-- Prove2me | Theorems.Thm_GlobalTheory_Conv_halfRing_spec
-- name    : GlobalTheory.Conv.halfRing_spec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:16.371804+00:00
-- url     : https://prove2.me/theorems/8779c20e-d312-4f1c-a654-12c3d89dc88e
-- title:
--   Conv: half Ring spec
-- statement:
--   The Conv construction uses the half Ring spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L369-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean#L369-L397

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology
open Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (eTwoPi SumsAt)
noncomputable section
open GlobalTheory GlobalTheory.Conv

theorem GlobalTheory.Conv.halfRing_spec :
    (∀ (T : ℝ) (s : ℂ⸨X⸩), s ∈ halfRing T ↔
      ∀ w : ℂ, T < w.im → Summable fun n : ℤ => s.coeff n * eTwoPi w ^ n) ∧
    (∀ (T : ℝ) (w : ℂ) (hw : T < w.im) (s : halfRing T),
      HasSum (fun n : ℤ => (s : ℂ⸨X⸩).coeff n * eTwoPi w ^ n) (ev T w hw s)) ∧
    (∀ (T : ℝ) (s : halfRing T), ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {w : ℂ | T < w.im} ∧
      ∀ w (hw : T < w.im), F w = ev T w hw s) ∧
    (∀ (T T' : ℝ) (s : halfRing T),
      (∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s = 0) → s = 0) ∧
    (∀ (T : ℝ) (s : halfRing T), s ≠ 0 →
      ∃ T' ≥ T, ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ev T w hw s ≠ 0) ∧
    Monotone halfRing ∧
    (⋃ T, (halfRing T : Set ℂ⸨X⸩) = convLaurent) ∧
    (∀ A : Subalgebra ℂ ℂ⸨X⸩, A.FG → A ≤ convLaurent.toSubalgebra → ∃ T, A ≤ halfRing T) ∧
    (∀ (T : ℝ) (s : halfRing T), (locRing T s).toSubring =
      Subring.closure ((halfRing T : Set ℂ⸨X⸩) ∪ {(s : ℂ⸨X⸩)⁻¹})) ∧
    (∀ (T : ℝ) (s : halfRing T), s ≠ 0 → IsLocalization.Away s (locRing T s)) ∧
    (∀ (T : ℝ) (w : ℂ) (hw : T < w.im) (s : halfRing T), ev T w hw s ≠ 0 →
      ∃! φ : locRing T s →ₐ[ℂ] ℂ, ∀ f, φ (algebraMap _ _ f) = ev T w hw f) ∧
    (∀ (T : ℝ) (w : ℂ) (hw : T < w.im) (p : ℂ⟦X⟧) (hp : (p : ℂ⸨X⸩) ∈ halfRing T),
      SumsAt p w (ev T w hw ⟨p, hp⟩)) := by sorry
