-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_exists_flagCover
-- name    : GlobalTheory.CompanionTheory.Ar.PB.exists_flagCover
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:21.05694+00:00
-- url     : https://prove2.me/theorems/b93b8aa9-08ec-4eb8-b927-e4aeff3aa337
-- title:
--   PB: exists flag Cover
-- statement:
--   The PB construction uses the exists flag Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/ExistsFlagModelBaseMetric.lean#L300-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/ExistsFlagModelBaseMetric.lean#L300-L323

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

theorem GlobalTheory.CompanionTheory.Ar.PB.exists_flagCover (ha : FlagModelExists) (hb : CoverExists) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {M : FlagModel y (CMType H) (D.p + D.q) D.p}
    {𝔐 : HodgeCpt Y S M.x} (tie : FlagTie M 𝔐) (A : HodgeCpt Y S' x₀) {κ : NonPluckerBlocks M.blk → K₀}
    {v : (Σ k, baseIdx ι M.blk k) → Σ k, J₀ k} {i : M.Ω →+* Ω} {h : A.X ⟶ 𝔐.X} {j : 𝔐.Li →+ A.Li} {n d d' : ℕ}
    (hκ : IsBlockMap κ v) (hx : ∀ q, x₀ (v q) = i (M.x q)) (ho : HodgeOver A 𝔐 h i j)
    (hv : IsArithVar (mCoordIdeal x₀) (n + 1)) (hd : 𝔐.IsCover d) (hd' : A.IsCover d') :
    ∃ (K' : Type) (_ : Fintype K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (Φ' : Type) (_ : Field Φ')
      (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' (CMType H) (D.p + D.q) D.p) (Cv : FlagCover M' M)
      (𝔐' : HodgeCpt Y S' y') (Fl : 𝔐'.Flag), d * Cv.deg = Fl.deg := by sorry
