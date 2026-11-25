-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_exists_flagModel_baseMetric
-- name    : GlobalTheory.CompanionTheory.Ar.PB.exists_flagModel_baseMetric
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:41.2196+00:00
-- url     : https://prove2.me/theorems/38eb3c39-cf92-4d97-8186-000d77989de8
-- title:
--   PB: exists flag Model base Metric
-- statement:
--   The PB construction uses the exists flag Model base Metric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/ExistsFlagModelBaseMetric.lean#L286-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/ExistsFlagModelBaseMetric.lean#L286-L298

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

theorem GlobalTheory.CompanionTheory.Ar.PB.exists_flagModel_baseMetric (ha : FlagModelExists) (hc : BaseMetricExists) (𝔐 : HodgeCpt Y S x₀) {d : ℕ}
    (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) (hv : IsArithVar (mCoordIdeal x₀) (Fintype.card (CMType H) * D.p * D.q + 1))
    (hd : 𝔐.IsCover d) (hs : HasSncBoundary 𝔐 (Fintype.card (CMType H) * D.p * D.q)) :
    ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (Φ : Type) (_ : Field Φ)
      (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐₁ : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐₁)
      (BM : BaseMetric M (Fintype.card (CMType H) * D.p * D.q)), BM.IsHodge tie ∧ BM.IsConj ∧
      IsArithVar (mCoordIdeal y)
        (Fintype.card (CMType H) * D.p * D.q + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by sorry
