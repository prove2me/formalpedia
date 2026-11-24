-- Prove2me | Theorems.Thm_GlobalTheory_Published_Heisenberg_mul_eq_central_mul
-- name    : GlobalTheory.Published.Heisenberg.mul_eq_central_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:09.018786+00:00
-- url     : https://prove2.me/theorems/7bb3fea6-2356-483c-b399-73024302b177
-- title:
--   Heisenberg: mul eq central mul
-- statement:
--   The Heisenberg construction uses the mul eq central mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean#L41-L45

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

theorem GlobalTheory.Published.Heisenberg.mul_eq_central_mul (h2 : (2 : F) ≠ 0) (hB : B.IsAlt) (g h : Heisenberg B) :
    g * h = (⟨0, B g.vec h.vec⟩ : Heisenberg B) * (h * g) := by sorry
