-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_jet_mk_eq_iff
-- name    : GlobalTheory.JetSer.jet_mk_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:12:04.090198+00:00
-- url     : https://prove2.me/theorems/ed9f042c-f90c-4630-89cf-c4f1a1f36347
-- title:
--   Jet Ser: jet mk eq iff
-- statement:
--   The Jet Ser construction uses the jet mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsToJetEq.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsToJetEq.lean#L10-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}

theorem GlobalTheory.JetSer.jet_mk_eq_iff (m : ℕ) (P Q : MvPolynomial κ R) :
    (Ideal.Quotient.mk _ P : JetR R κ m) = Ideal.Quotient.mk _ Q ↔
      ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → P.coeff e = Q.coeff e := by sorry
