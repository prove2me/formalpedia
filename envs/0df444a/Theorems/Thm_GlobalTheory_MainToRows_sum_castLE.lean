-- Prove2me | Theorems.Thm_GlobalTheory_MainToRows_sum_castLE
-- name    : GlobalTheory.MainToRows.sum_castLE
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:19:43.525799+00:00
-- url     : https://prove2.me/theorems/180f0728-b77b-4332-bec4-a88ca3203390
-- title:
--   Main To Rows: sum cast LE
-- statement:
--   The Main To Rows construction uses the sum cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MainTermImpliesRowHypothesis.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MainTermImpliesRowHypothesis.lean#L46-L49

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open scoped BigOperators
open Classical MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open GlobalTheory GlobalTheory.MainToRows
variable {C : Type} [Field C]

theorem GlobalTheory.MainToRows.sum_castLE {M : Type*} [AddCommMonoid M] {n0 n : ℕ} (hn : n0 ≤ n) (f : Fin n → M)
    (hf : ∀ b, b ∉ Set.range (Fin.castLE hn) → f b = 0) :
    ∑ b, f b = ∑ b : Fin n0, f (Fin.castLE hn b) := by sorry
