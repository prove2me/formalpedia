-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_CoverExists_diag
-- name    : GlobalTheory.CompanionTheory.Ar.PB.CoverExists.diag
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:00:06.846815+00:00
-- url     : https://prove2.me/theorems/afdbfabf-5ba2-5a63-ab81-7cc8663cff50
-- title:
--   Cover Exists: diag
-- statement:
--   The Cover Exists construction uses the diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/ExistsFlagModelBaseMetric.lean#L325-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/ExistsFlagModelBaseMetric.lean#L325-L334

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_ExistsFlagModelBaseMetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S S' : Finset ℕ}
  {Ω : Type} [Field Ω] [CharZero Ω] {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {x₀ : (Σ k, J₀ k) → Ω}

theorem GlobalTheory.CompanionTheory.Ar.PB.CoverExists.diag (hb : CoverExists) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type}
    [Field Φ] {y : (Σ k, ι k) → Φ} {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}
    (tie : FlagTie M 𝔐) {d : ℕ} (hd : 𝔐.IsCover d) :
    ∃ Cv : FlagCover M M, Cv.v = id ∧ d * Cv.deg = d ∧ Cv.deg = 1 := by sorry
