-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CofinalDual_index_eq_of_pairing
-- name    : GlobalTheory.CompanionTheory.SW.CofinalDual.index_eq_of_pairing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:26.032731+00:00
-- url     : https://prove2.me/theorems/77d7bb96-d312-4620-9f90-0906977e050e
-- title:
--   Cofinal Dual: index eq of pairing
-- statement:
--   The Cofinal Dual construction uses the index eq of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AnnihilatorOfAnnihilatorLe.lean#L37-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AnnihilatorOfAnnihilatorLe.lean#L37-L83

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

theorem GlobalTheory.CompanionTheory.SW.CofinalDual.index_eq_of_pairing {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (c : X → Y → ℂ)
    (hn : ∀ x y, ‖c x y‖ = 1)
    (hl : ∀ x x' y, c (x + x') y = c x y * c x' y)
    (hr : ∀ x y y', c x (y + y') = c x y * c x y')
    (N : AddSubgroup X) (M : AddSubgroup Y)
    (hN : ∀ x, x ∈ N ↔ ∀ y, c x y = 1) (hM : ∀ y, y ∈ M ↔ ∀ x, c x y = 1)
    [N.FiniteIndex] [M.FiniteIndex] : N.index = M.index := by sorry
