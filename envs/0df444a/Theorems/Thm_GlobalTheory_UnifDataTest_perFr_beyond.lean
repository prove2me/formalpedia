-- Prove2me | Theorems.Thm_GlobalTheory_UnifDataTest_perFr_beyond
-- name    : GlobalTheory.UnifDataTest.perFr_beyond
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:45:28.59413+00:00
-- url     : https://prove2.me/theorems/4e16d2c3-3452-5c19-b18f-9824a162f092
-- title:
--   Unif Data Test: per Fr beyond
-- statement:
--   The Unif Data Test construction uses the per Fr beyond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RelabBijective.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RelabBijective.lean#L89-L96

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

theorem GlobalTheory.UnifDataTest.perFr_beyond (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) {τ : E →+* ℂ} (h : τ ∉ X.Ψ) (hr : 0 < r)
    {i : ℕ} (hi : X.p0 ≤ i + 1) :
    perFr X x v τ i =
      hermC (conjEmb τ) X.Gm (col (mat x ⟨conjEmb τ, conj_mem X h⟩) ⟨0, hr⟩) (Data.emb (conjEmb τ) v) := by sorry
