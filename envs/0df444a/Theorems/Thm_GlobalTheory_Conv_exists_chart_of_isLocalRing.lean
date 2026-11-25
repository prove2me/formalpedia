-- Prove2me | Theorems.Thm_GlobalTheory_Conv_exists_chart_of_isLocalRing
-- name    : GlobalTheory.Conv.exists_chart_of_isLocalRing
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:08.866798+00:00
-- url     : https://prove2.me/theorems/4fa844af-88e8-42ab-837e-b6c7863ce0e7
-- title:
--   Conv: exists chart of is Local Ring
-- statement:
--   The Conv construction uses the exists chart of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L1059-L1080
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean#L1059-L1080

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology ENNReal NNReal ContDiff
open Filter Metric
noncomputable section
open GlobalTheory GlobalTheory.Conv
open CategoryTheory AlgebraicGeometry

theorem GlobalTheory.Conv.exists_chart_of_isLocalRing {Y : Scheme.{0}} (s : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType s] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℂ R]
    (x : Spec (.of R) ⟶ Y) (hx : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :
    ∃ (A : CommRingCat.{0}) (_ : Algebra ℂ A) (_ : Algebra.FiniteType ℂ A) (i : Spec A ⟶ Y)
      (φ : A →ₐ[ℂ] R), IsOpenImmersion i ∧
        i ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) ∧
        Spec.map (CommRingCat.ofHom (φ : A →+* R)) ≫ i = x := by sorry
