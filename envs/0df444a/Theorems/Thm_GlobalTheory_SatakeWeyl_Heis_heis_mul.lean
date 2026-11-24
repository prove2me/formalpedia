-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_heis_mul
-- name    : GlobalTheory.SatakeWeyl.Heis.heis_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:48:32.31982+00:00
-- url     : https://prove2.me/theorems/5e942ad1-d629-4a01-b9ba-1a97f0ca0750
-- title:
--   Heis: heis mul
-- statement:
--   The Heis construction uses the heis mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L107-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L107-L111

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
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.SatakeWeyl.Heis.heis_mul (x y x' y' : L) :
    Heisenberg₂ σ x y * Heisenberg₂ σ x' y' = Heisenberg₂ σ (x + x') (y + y' - x * σ x') := by sorry
