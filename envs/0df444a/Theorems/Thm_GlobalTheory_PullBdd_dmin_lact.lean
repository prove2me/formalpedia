-- Prove2me | Theorems.Thm_GlobalTheory_PullBdd_dmin_lact
-- name    : GlobalTheory.PullBdd.dmin_lact
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:39.024373+00:00
-- url     : https://prove2.me/theorems/0bbcc070-2053-46a8-964d-cd7fa56259c9
-- title:
--   Pull Bdd: dmin lact
-- statement:
--   The Pull Bdd construction uses the dmin lact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSection.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSection.lean#L47-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix
open GlobalTheory GlobalTheory.PullBdd
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.PullBdd.dmin_lact {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {β : GL (Fin r) E}
    (hβ : ∀ u v, herm G ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm G u v) (x : Frame Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (lact β x) τ i = dmin G x τ i := by sorry
