-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_Low_term
-- name    : GlobalTheory.MinorGerm.Low.term
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:48:03.144018+00:00
-- url     : https://prove2.me/theorems/b8e084bb-0a4c-4550-882a-24bf627bdae7
-- title:
--   Low: term
-- statement:
--   The Low construction uses the term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L22-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L22-L43

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}

theorem GlobalTheory.MinorGerm.Low.term {α β : σ →₀ ℕ} {g h : MvPowerSeries σ C} (hg : Low α g) (hh : Low β h)
    (a b : σ →₀ ℕ) (hd : a.degree + b.degree ≤ α.degree + β.degree) (hne : (a, b) ≠ (α, β)) :
    MvPowerSeries.coeff a g * MvPowerSeries.coeff b h = 0 := by sorry
