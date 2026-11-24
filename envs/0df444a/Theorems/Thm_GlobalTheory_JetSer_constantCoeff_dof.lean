-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_constantCoeff_dof
-- name    : GlobalTheory.JetSer.constantCoeff_dof
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:42:48.916741+00:00
-- url     : https://prove2.me/theorems/15f0adc3-61ae-47cf-8feb-b94697d75af9
-- title:
--   Jet Ser: constant Coeff dof
-- statement:
--   The Jet Ser construction uses the constant Coeff dof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DualNumberValueToJet.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DualNumberValueToJet.lean#L33-L47

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

theorem GlobalTheory.JetSer.constantCoeff_dof {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d : ℕ}
    (G : FGLaw R d) (e : Fin d → O) (u : PS O 1 d) :
    constantCoeff (Dof (G.mapF f) e u) =
      ∑ j, e j * coeff (Finsupp.single ((0 : Fin 1), j) 1) u := by sorry
