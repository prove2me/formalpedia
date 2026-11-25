-- Prove2me | Theorems.Thm_GlobalTheory_SigmaDefect_sgOf_defect
-- name    : GlobalTheory.SigmaDefect.sgOf_defect
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:51.967857+00:00
-- url     : https://prove2.me/theorems/88faccae-a642-431d-8683-76aa0706ccd0
-- title:
--   Sigma Defect: sg Of defect
-- statement:
--   The Sigma Defect construction uses the sg Of defect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/SigmaDefectEvalPhaseOne.lean#L51-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/SigmaDefectEvalPhaseOne.lean#L51-L75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
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
open GlobalTheory GlobalTheory.SigmaDefect
open GlobalTheory.QuadDeriv GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem GlobalTheory.SigmaDefect.sgOf_defect (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (i : Fin d) :
    ev ![B.FK k] (sgOf k h i) = ev (n := 2) ![pt k d 0] (sgOf k h i) +
      ev (n := 2) ![pt k d 1] (sgOf k h i) +
      ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) (FB.toK k B.ph1)) := by sorry
