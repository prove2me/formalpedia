-- Prove2me | Theorems.Thm_GlobalTheory_IntegralColumnGerm_prod_pow_sub_one_mem
-- name    : GlobalTheory.IntegralColumnGerm.prod_pow_sub_one_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:52:46.640799+00:00
-- url     : https://prove2.me/theorems/dd25ddfe-99cd-4616-9472-a7f220d6c8a7
-- title:
--   Integral Column Germ: prod pow sub one mem
-- statement:
--   The Integral Column Germ construction uses the prod pow sub one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralGermNabValCongr.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralGermNabValCongr.lean#L19-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralGermNabValCongr
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
open GlobalTheory GlobalTheory.IntegralColumnGerm

theorem GlobalTheory.IntegralColumnGerm.prod_pow_sub_one_mem {R : Type} [CommRing R] (I : Ideal R) {ι : Type} [Fintype ι] (α : ι → R)
    (hα : ∀ l, α l - 1 ∈ I) (n : ι → ℕ) : ∏ l, α l ^ n l - 1 ∈ I := by sorry
