-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_immersion_inl
-- name    : GlobalTheory.CompanionTheory.Ar.Giv.ResProj.immersion_inl
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:20:07.348315+00:00
-- url     : https://prove2.me/theorems/c6fa9d26-06e2-4225-aa01-314adf70bd77
-- title:
--   Res Proj: immersion inl
-- statement:
--   The Res Proj construction uses the immersion inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean#L227-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean#L227-L320

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Giv
open GlobalTheory.CompanionTheory.Ar.Giv.ResProj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
variable {M : ℕ}
local notation "𝔅" => (fun _ : Unit => Fin M)

theorem GlobalTheory.CompanionTheory.Ar.Giv.ResProj.immersion_inl {e : ℕ} {Y : Type} [TopologicalSpace Y] {A : FinHolAtlas e Y}
    {P' : Ideal (MRing (joinIdx ι 𝔅))} {U : Y → Set Y} {lam : Y → Y → (Σ k, joinIdx ι 𝔅 k) → ℂ}
    (hE : IsEmbedded A P' U lam) {G : Fin M → MRing ι} {g : K → ℕ} (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ z ∈ mcPts P', ∀ i j : Fin M, z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι 𝔅) (G j) =
      z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι 𝔅) (G i))
    (x : Y) (l : Fin M) (hl : lam x x ⟨Sum.inr (), l⟩ ≠ 0) (hGl : evC (lam x x ∘ joinInl ι 𝔅) (G l) ≠ 0)
    (p : (k : K) → ι k) (hp : ∀ k, lam x x ⟨Sum.inl k, p k⟩ ≠ 0) (j : Fin A.n) (hx : x ∈ (A.chart j).source) :
    (fderiv ℂ (fun t => affCoord p (lam x ((A.chart j).symm t) ∘ joinInl ι 𝔅)) (A.chart j x)).ker = ⊥ := by sorry
