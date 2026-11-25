-- Prove2me | Theorems.Thm_GlobalTheory_CoeffRingTest_zeta_pd_mem
-- name    : GlobalTheory.CoeffRingTest.zeta_pd_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:56.136442+00:00
-- url     : https://prove2.me/theorems/379522fb-efc9-55ea-b1be-c04c3efc20a8
-- title:
--   Coeff Ring Test: zeta pd mem
-- statement:
--   The Coeff Ring Test construction uses the zeta pd mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/FullIffBijective.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/FullIffBijective.lean#L37-L41

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_FullIffBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffRingTest
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem GlobalTheory.CoeffRingTest.zeta_pd_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (h : d.IsLev) : zeta d.pd ∈ c.F := by sorry
