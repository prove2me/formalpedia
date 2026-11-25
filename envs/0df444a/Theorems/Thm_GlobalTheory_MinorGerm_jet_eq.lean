-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_jet_eq
-- name    : GlobalTheory.MinorGerm.jet_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:40.809811+00:00
-- url     : https://prove2.me/theorems/0e7d5c40-d320-47a0-b5b3-4dfdcb3f4e1a
-- title:
--   Minor Germ: jet eq
-- statement:
--   The Minor Germ construction uses the jet eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L174-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L174-L191

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
variable {p : σ → Prop} [DecidablePred p]

theorem GlobalTheory.MinorGerm.jet_eq {α : σ →₀ ℕ} {P : MvPolynomial σ C} {g : MvPowerSeries σ C} (hP : Lead p α P)
    (hg : Low α g) : jetAt0 P g = (mfact α : C) := by sorry
