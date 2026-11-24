-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_unif
-- name    : GlobalTheory.ThK.Dbl.LD.sb_unif
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:38.487938+00:00
-- url     : https://prove2.me/theorems/5a205e47-6a4f-4c6f-b54e-504be7d56c26
-- title:
--   LD: sb unif
-- statement:
--   The LD construction uses the sb unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean#L49-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD

theorem GlobalTheory.ThK.Dbl.LD.sb_unif {X P : Type} [TopologicalSpace X] [TopologicalSpace P] {φ : X → ℂ} (hφ : φ ∈ SB X) (a : P → X → X) (p : P)
    (ha : Continuous fun z : P × X => a z.1 z.2) (h0 : ∀ x, a p x = x) :
    ∀ᶠ k in 𝓝 p, ∀ x ∈ tsupport φ, φ (a k x) = φ x := by sorry
