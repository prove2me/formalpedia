-- Prove2me | Theorems.Thm_GlobalTheory_LogLinear_eq_zero_of_additive
-- name    : GlobalTheory.LogLinear.eq_zero_of_additive
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:50:41.276085+00:00
-- url     : https://prove2.me/theorems/9e6a00d0-4849-4799-b985-79eaeb95d70b
-- title:
--   Log Linear: eq zero of additive
-- statement:
--   The Log Linear construction uses the eq zero of additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalGroupLogEndomorphismLinear.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalGroupLogEndomorphismLinear.lean#L16-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqZeroOfAdditiveOfPderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalGroupLogEndomorphismLinear
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.LogLinear
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.LogLinear.eq_zero_of_additive [Algebra ℚ k] (G : FGLaw k d) (g : PS k 1 d)
    (hadd : ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] g =
      ev (n := 2) ![pt k d 0] g + ev (n := 2) ![pt k d 1] g)
    (hlin : ∀ i, coeff (Finsupp.single ((0 : Fin 1), i) 1) g = 0) : g = 0 := by sorry
