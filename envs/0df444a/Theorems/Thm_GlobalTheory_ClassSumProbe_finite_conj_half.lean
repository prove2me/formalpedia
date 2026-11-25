-- Prove2me | Theorems.Thm_GlobalTheory_ClassSumProbe_finite_conj_half
-- name    : GlobalTheory.ClassSumProbe.finite_conj_half
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:04.886508+00:00
-- url     : https://prove2.me/theorems/bc2b3ee2-ed96-4bb6-985b-158962620c50
-- title:
--   Class Sum Probe: finite conj half
-- statement:
--   The Class Sum Probe construction uses the finite conj half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/TransformIndicator.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/TransformIndicator.lean#L27-L32

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_TransformIndicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassSumProbe
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
set_option autoImplicit false
open NumberField MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem GlobalTheory.ClassSumProbe.finite_conj_half :
    Finite (Dw.La ⧸ (_root_.Formalism.L2.Pj.Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) := by sorry
