-- Prove2me | Theorems.Thm_GlobalTheory_LocMod_Inhab_sb_le
-- name    : GlobalTheory.LocMod.Inhab.sb_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:58.052847+00:00
-- url     : https://prove2.me/theorems/208b3103-93c6-4af3-a5ea-35a8db38276d
-- title:
--   Inhab: sb le
-- statement:
--   The Inhab construction uses the sb le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L140-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/InvariantOfTsupport.lean#L140-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem GlobalTheory.LocMod.Inhab.sb_le {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {N : Submodule ℂ (Matrix Y Y' k → ℂ)}
    (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hN' : ∀ y, ∀ Φ ∈ N, (fun t => pairing ψ t y * Φ t) ∈ N)
    {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (h0 : Φ ≠ 0) (hΦN : Φ ∈ N) : SB (Matrix Y Y' k) ≤ N := by sorry
