-- Prove2me | Theorems.Thm_GlobalTheory_CrudeValue_constantCoeff_ev_eq_zero
-- name    : GlobalTheory.CrudeValue.constantCoeff_ev_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:46.34146+00:00
-- url     : https://prove2.me/theorems/26f8184b-940e-4358-960f-f9ff345c61be
-- title:
--   Crude Value: constant Coeff ev eq zero
-- statement:
--   The Crude Value construction uses the constant Coeff ev eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdNabValLeadingMinors.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdNabValLeadingMinors.lean#L24-L31

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

theorem GlobalTheory.CrudeValue.constantCoeff_ev_eq_zero {m n : ℕ} (a : Fin m → Pt k n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS k m d) (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by sorry
