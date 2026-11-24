-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CofinalDual_card_le_of_pairing
-- name    : GlobalTheory.CompanionTheory.SW.CofinalDual.card_le_of_pairing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:39.37309+00:00
-- url     : https://prove2.me/theorems/ea38688a-29f8-423b-9ff1-737b7f638c43
-- title:
--   Cofinal Dual: card le of pairing
-- statement:
--   The Cofinal Dual construction uses the card le of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AnnihilatorOfAnnihilatorLe.lean#L9-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AnnihilatorOfAnnihilatorLe.lean#L9-L35

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

theorem GlobalTheory.CompanionTheory.SW.CofinalDual.card_le_of_pairing {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
    (b : A → B → ℂ) (hn : ∀ x y, ‖b x y‖ = 1)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (hk : ∀ x, (∀ y, b x y = 1) → x = 0) : Nat.card A ≤ Nat.card B := by sorry
