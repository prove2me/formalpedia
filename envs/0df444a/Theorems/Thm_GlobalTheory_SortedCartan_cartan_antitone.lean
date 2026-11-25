-- Prove2me | Theorems.Thm_GlobalTheory_SortedCartan_cartan_antitone
-- name    : GlobalTheory.SortedCartan.cartan_antitone
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:28:43.359696+00:00
-- url     : https://prove2.me/theorems/909f4cc8-9f27-5025-9a5e-d2d3a4168d3f
-- title:
--   Sorted Cartan: cartan antitone
-- statement:
--   The Sorted Cartan construction uses the cartan antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CartanAntitone.lean#L52-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CartanAntitone.lean#L52-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_IsCoType
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CartanAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
noncomputable section
open GlobalTheory GlobalTheory.SortedCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SortedCartan.cartan_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), x = κ * torusElt k (Fin N) ϖ ν * κ' := by sorry
