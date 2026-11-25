-- Prove2me | Theorems.Thm_GlobalTheory_CrudeValue_constantCoeff_hL
-- name    : GlobalTheory.CrudeValue.constantCoeff_hL
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:00.535658+00:00
-- url     : https://prove2.me/theorems/c3e6a239-e6a9-42d5-97b9-afed934356e8
-- title:
--   Crude Value: constant Coeff h L
-- statement:
--   The Crude Value construction uses the constant Coeff h L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdNabValLeadingMinors.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdNabValLeadingMinors.lean#L37-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdNabValLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.CrudeValue
variable {k : Type} [CommRing k] {d : ℕ}
variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] [Algebra ℚ k] [Algebra R k]
omit [Algebra ℚ k]

theorem GlobalTheory.CrudeValue.constantCoeff_hL (B : FB R d O) (h : PS k 2 d) (hh : constantCoeff h = 0) (w0 : O) :
    constantCoeff (B.hL k h w0) = 0 := by sorry
