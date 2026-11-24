-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_conj_iff
-- name    : GlobalTheory.SatakeWeyl.Heis.conj_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:47:42.785822+00:00
-- url     : https://prove2.me/theorems/db6d58bf-1680-44dd-8442-7c94946abbf2
-- title:
--   Heis: conj iff
-- statement:
--   The Heis construction uses the conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L96-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L96-L104

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

theorem GlobalTheory.SatakeWeyl.Heis.conj_iff {ϖ : L} (h0 : ϖ ≠ 0) (hϖ : σ ϖ = ϖ) {s : GU σ 3}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ (![1, 0, -1] : Fin 3 → ℤ) i)) (g : GU σ 3) (x y : L)
    (e : mat g = Heisenberg₂ σ x y) : mat (s * g * s⁻¹) = Heisenberg₂ σ (ϖ * x) (ϖ * (ϖ * y)) := by sorry
