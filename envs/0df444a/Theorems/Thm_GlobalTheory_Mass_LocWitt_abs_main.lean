-- Prove2me | Theorems.Thm_GlobalTheory_Mass_LocWitt_abs_main
-- name    : GlobalTheory.Mass.LocWitt.abs_main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:45.558965+00:00
-- url     : https://prove2.me/theorems/2154b19e-170f-4adc-a8e3-cbeb9f5e9bce
-- title:
--   Loc Witt: abs main
-- statement:
--   The Loc Witt construction uses the abs main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean#L62-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemHcompl.lean#L62-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LocWitt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.Mass.LocWitt.abs_main {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {Λ : AddSubgroup V} {A : Subring K}
    {M : AddSubgroup K}
    (hA : ∀ a ∈ A, star a ∈ A) (hΛ : ∀ a ∈ A, ∀ v ∈ Λ, a • v ∈ Λ) (hi : ∀ v ∈ Λ, ∀ w ∈ Λ, h v w ∈ A)
    (hM : ∀ a ∈ A, ∀ m ∈ M, a * m ∈ M) (h1 : (1 : K) ∉ M) (hinv : ∀ a ∈ A, a ∉ M → a⁻¹ ∈ A)
    {θ : K} (hθ : θ ∈ A) (hδ : θ - star θ ∉ M)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) (hn : h x x = h y y)
    (px : ∃ w ∈ Λ, h w x = 1) (py : ∃ w ∈ Λ, h w y = 1) : Rel h Λ x y := by sorry
