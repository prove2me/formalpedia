-- Prove2me | Theorems.Thm_GlobalTheory_UnifDataTest_laU_lower
-- name    : GlobalTheory.UnifDataTest.laU_lower
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:22.000362+00:00
-- url     : https://prove2.me/theorems/9015f2bd-68a3-4525-91f8-86e42a811111
-- title:
--   Unif Data Test: la U lower
-- statement:
--   The Unif Data Test construction uses the la U lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RelabBijective.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RelabBijective.lean#L33-L38

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

theorem GlobalTheory.UnifDataTest.laU_lower (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) (τ : E →+* ℂ)
    (hτ : relab c σ τ ∈ (U.X k).Ψ) (i : ℕ) (hi : i < (U.X k).p0) (hr : (U.X k).p0 - 1 - i < r) :
    laU U a n k ⟨_, hτ⟩ ⟨_, hr⟩ = -(a (conjEmb τ, i) : ℤ) - (n / 2 : ℕ) := by sorry
