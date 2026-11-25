-- Prove2me | Theorems.Thm_GlobalTheory_UnifDataTest_laU_antitone
-- name    : GlobalTheory.UnifDataTest.laU_antitone
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:23.041646+00:00
-- url     : https://prove2.me/theorems/22bae178-77a2-41e3-9f1e-89433dcb257f
-- title:
--   Unif Data Test: la U antitone
-- statement:
--   The Unif Data Test construction uses the la U antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RelabBijective.lean#L40-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RelabBijective.lean#L40-L56

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

theorem GlobalTheory.UnifDataTest.laU_antitone (U : Unf Xo c σ r) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n) (k : U.Comp)
    (τ : (U.X k).Ψ) (j j' : Fin r) (hj : j ≤ j') (hb : (U.X k).p0 ≤ (j : ℕ) ∨ (j' : ℕ) < (U.X k).p0) :
    laU U a n k τ j' ≤ laU U a n k τ j := by sorry
