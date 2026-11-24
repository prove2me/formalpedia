-- Prove2me | Theorems.Thm_GlobalTheory_Published_SvN_exists_selfDual
-- name    : GlobalTheory.Published.SvN.exists_selfDual
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:57:57.330798+00:00
-- url     : https://prove2.me/theorems/30b1cf10-454c-44dc-bf58-30abe31b1c97
-- title:
--   Sv N: exists self Dual
-- statement:
--   The Sv N construction uses the exists self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L250-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L250-L268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}

theorem GlobalTheory.Published.SvN.exists_selfDual (h : Alt c) (L : AddSubgroup W) (hL : L ≤ h.perp L) :
    ∃ A : AddSubgroup W, L ≤ A ∧ A ≤ h.perp A ∧ h.perp A ≤ A := by sorry
