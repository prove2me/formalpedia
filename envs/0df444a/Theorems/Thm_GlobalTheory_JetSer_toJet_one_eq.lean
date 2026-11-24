-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_toJet_one_eq
-- name    : GlobalTheory.JetSer.toJet_one_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:42:29.516368+00:00
-- url     : https://prove2.me/theorems/2b0623cb-cfeb-4302-8fef-a2502026dbe6
-- title:
--   Jet Ser: to Jet one eq
-- statement:
--   The Jet Ser construction uses the to Jet one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DualNumberValueToJet.lean#L10-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DualNumberValueToJet.lean#L10-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DualNumberValueToJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer

theorem GlobalTheory.JetSer.toJet_one_eq {O κ : Type} [CommRing O] [Fintype κ] (u : MvPowerSeries κ O) :
    toJet 1 u = Ideal.Quotient.mk _ (MvPolynomial.C (constantCoeff u) +
      ∑ q, MvPolynomial.C (coeff (Finsupp.single q 1) u) * MvPolynomial.X q) := by sorry
