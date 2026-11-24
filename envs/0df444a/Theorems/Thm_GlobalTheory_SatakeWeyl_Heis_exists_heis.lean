-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_exists_heis
-- name    : GlobalTheory.SatakeWeyl.Heis.exists_heis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:47:54.29091+00:00
-- url     : https://prove2.me/theorems/62ebd3d8-502a-4a99-ad59-6d5e973dbaee
-- title:
--   Heis: exists heis
-- statement:
--   The Heis construction uses the exists heis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L66-L76

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem GlobalTheory.SatakeWeyl.Heis.exists_heis (hσ : ∀ x, σ (σ x) = x) {x y : L} (h : y + σ y + x * σ x = 0) :
    ∃ g : GU σ 3, mat g = Heisenberg₂ σ x y := by sorry
