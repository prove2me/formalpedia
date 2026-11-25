-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_suppCol_of_oneIndexAt
-- name    : GlobalTheory.LocFlat.suppCol_of_oneIndexAt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:19:55.391588+00:00
-- url     : https://prove2.me/theorems/36d0e04a-066c-5207-9c16-bc3ab69cdbdf
-- title:
--   Loc Flat: supp Col of one Index At
-- statement:
--   The Loc Flat construction uses the supp Col of one Index At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnSupportOfOneIndexAtSymPosition.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnSupportOfOneIndexAtSymPosition.lean#L31-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnSupportOfOneIndexAtSymPosition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory.LocFlat.SuppColProof

theorem GlobalTheory.LocFlat.suppCol_of_oneIndexAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneIndexAt t ν → GlobalTheory.LocFlat.SuppCol S t ν := by sorry
