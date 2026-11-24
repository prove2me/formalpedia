-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CofinalDual_relIndex_eq_of_pairing
-- name    : GlobalTheory.CompanionTheory.SW.CofinalDual.relIndex_eq_of_pairing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:33.245745+00:00
-- url     : https://prove2.me/theorems/0914d4ee-82ee-45cd-8d80-05299da71bd7
-- title:
--   Cofinal Dual: rel Index eq of pairing
-- statement:
--   The Cofinal Dual construction uses the rel Index eq of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AnnihilatorOfAnnihilatorLe.lean#L168-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AnnihilatorOfAnnihilatorLe.lean#L168-L186

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CofinalDual

theorem GlobalTheory.CompanionTheory.SW.CofinalDual.relIndex_eq_of_pairing {V : Type} [AddCommGroup V] (χ : V → V → ℂ)
    (hs : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1)
    (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (X₀ X Y₀ Y : AddSubgroup V)
    (hX : ∀ x ∈ X, (x ∈ X₀ ↔ ∀ y ∈ Y, χ x y = 1))
    (hY : ∀ y ∈ Y, (y ∈ Y₀ ↔ ∀ x ∈ X, χ x y = 1))
    (fX : X₀.relIndex X ≠ 0) (fY : Y₀.relIndex Y ≠ 0) : X₀.relIndex X = Y₀.relIndex Y := by sorry
