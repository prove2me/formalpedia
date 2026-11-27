-- Prove2me | Theorems.Thm_GlobalTheory_UnifDataTest_perFr_smul
-- name    : GlobalTheory.UnifDataTest.perFr_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:18.11506+00:00
-- url     : https://prove2.me/theorems/7286ee34-3f00-4d0f-9a13-0afacb5210c8
-- title:
--   Unif Data Test: per Fr smul
-- statement:
--   The Unif Data Test construction uses the per Fr smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RelabBijective.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RelabBijective.lean#L74-L87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RelabBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnifDataTest
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem GlobalTheory.UnifDataTest.perFr_smul (X : Data E r) (x : Frame X.Ψ r) (b : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x (b • v) τ i = τ b * perFr X x v τ i := by sorry
