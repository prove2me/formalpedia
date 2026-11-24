-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_wQ
-- name    : GlobalTheory.Ex.NumD.Int.norm_wQ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:07:18.05594+00:00
-- url     : https://prove2.me/theorems/0dc0f166-6f97-4d38-bcd7-767db11317d0
-- title:
--   Int: norm w Q
-- statement:
--   The Int construction uses the norm w Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormRepGeneratorsAndThetaSeriesTerm.lean#L43-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormRepGeneratorsAndThetaSeriesTerm.lean#L43-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem GlobalTheory.Ex.NumD.Int.norm_wQ (h : N.Int q) {k : ℕ} (hk : Odd k) (p : N.QT k) :
    ‖(N.wQ p : C)‖ = Real.exp (-(q p.1.1.toAdd / k)) := by sorry
