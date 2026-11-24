-- Prove2me | Theorems.Thm_GlobalTheory_SortedCartan_permUnit_val
-- name    : GlobalTheory.SortedCartan.permUnit_val
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:11:58.903541+00:00
-- url     : https://prove2.me/theorems/3c4cebcf-fe80-43da-a00a-f6b01a72c430
-- title:
--   Sorted Cartan: perm Unit val
-- statement:
--   The Sorted Cartan construction uses the perm Unit val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CartanAntitone.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CartanAntitone.lean#L28-L33

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

theorem GlobalTheory.SortedCartan.permUnit_val {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ((permUnit σ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = σ.toPEquiv.toMatrix := by sorry
