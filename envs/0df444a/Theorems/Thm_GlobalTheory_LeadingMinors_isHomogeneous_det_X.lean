-- Prove2me | Theorems.Thm_GlobalTheory_LeadingMinors_isHomogeneous_det_X
-- name    : GlobalTheory.LeadingMinors.isHomogeneous_det_X
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:14.352388+00:00
-- url     : https://prove2.me/theorems/b4f3cf69-fbaa-4f98-8cc0-90e01ead3a70
-- title:
--   Leading Minors: is Homogeneous det X
-- statement:
--   The Leading Minors construction uses the is Homogeneous det X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CoeffProdLeadingMinors.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CoeffProdLeadingMinors.lean#L10-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.LeadingMinors
open MvPowerSeries

theorem GlobalTheory.LeadingMinors.isHomogeneous_det_X {k σ ι : Type*} [CommRing k] [Fintype ι]
    [DecidableEq ι] (v : ι → ι → σ) :
    (Matrix.of fun a i : ι => (MvPolynomial.X (v a i) : MvPolynomial σ k)).det.IsHomogeneous
      (Fintype.card ι) := by sorry
