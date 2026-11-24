-- Prove2me | Theorems.Thm_GlobalTheory_Published_Heisenberg_mul_ne_mul
-- name    : GlobalTheory.Published.Heisenberg.mul_ne_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:11.031634+00:00
-- url     : https://prove2.me/theorems/2194e39d-eae1-4e0a-9139-8ba087f05802
-- title:
--   Heisenberg: mul ne mul
-- statement:
--   The Heisenberg construction uses the mul ne mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L47-L51

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
open GlobalTheory.Published.Heisenberg
variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W}

theorem GlobalTheory.Published.Heisenberg.mul_ne_mul (h2 : (2 : F) ≠ 0) (hB : B.IsAlt) {x y : W} (hxy : B x y ≠ 0) :
    (⟨x, 0⟩ : Heisenberg B) * ⟨y, 0⟩ ≠ ⟨y, 0⟩ * ⟨x, 0⟩ := by sorry
