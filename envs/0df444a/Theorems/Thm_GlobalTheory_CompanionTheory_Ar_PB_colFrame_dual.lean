-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_colFrame_dual
-- name    : GlobalTheory.CompanionTheory.Ar.PB.colFrame_dual
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:25.551968+00:00
-- url     : https://prove2.me/theorems/e7d7e763-ca2e-4fe2-a8b2-39015d7e17b0
-- title:
--   PB: col Frame dual
-- statement:
--   The PB construction uses the col Frame dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/ExistsFlagModelBaseMetric.lean#L209-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/ExistsFlagModelBaseMetric.lean#L209-L215

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
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S S' S'' : Finset ℕ}
  {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω''] {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : K → Type} {J' : K' → Type} {J'' : K'' → Type} {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'}
  {x'' : (Σ k, J'' k) → Ω''}
variable {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} {h : A'.X ⟶ A.X} {i : Ω →+* Ω'} {j : A.Li →+ A'.Li}

theorem GlobalTheory.CompanionTheory.Ar.PB.colFrame_dual {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ} (φ : Fin r → Module.Dual Ω V) (v : Fin r → V)
    (hv : ∀ a b, φ a (v b) = if a = b then 1 else 0) (g : Matrix (Fin r) (Fin r) Ω) (hg : IsUnit g.det) (k m : Fin r) :
    colFrame φ g k (colFrame v gᵀ⁻¹ m) = if k = m then 1 else 0 := by sorry
