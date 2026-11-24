-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_sameOrbit_of_inl
-- name    : GlobalTheory.CompanionTheory.Ar.Giv.ResProj.sameOrbit_of_inl
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:23:39.253807+00:00
-- url     : https://prove2.me/theorems/74b4cf25-3c67-4a72-8ea1-4d7b06967363
-- title:
--   Res Proj: same Orbit of inl
-- statement:
--   The Res Proj construction uses the same Orbit of inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean#L137-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean#L137-L169

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
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

theorem GlobalTheory.CompanionTheory.Ar.Giv.ResProj.sameOrbit_of_inl {G : Fin M → MRing ι} {g : K → ℕ} (hG : ∀ i, IsMultiHomog (G i) g)
    {z u : (Σ k, joinIdx ι 𝔅 k) → ℂ}
    (hzb : ∃ i : Fin M, z ⟨Sum.inr (), i⟩ ≠ 0) (hub : ∃ i : Fin M, u ⟨Sum.inr (), i⟩ ≠ 0)
    (hzc : ∀ i j : Fin M, z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι 𝔅) (G j) =
      z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι 𝔅) (G i))
    (huc : ∀ i j : Fin M, u ⟨Sum.inr (), i⟩ * evC (u ∘ joinInl ι 𝔅) (G j) =
      u ⟨Sum.inr (), j⟩ * evC (u ∘ joinInl ι 𝔅) (G i))
    (ho : SameOrbit (z ∘ joinInl ι 𝔅) (u ∘ joinInl ι 𝔅))
    {l : Fin M} (hl : evC (z ∘ joinInl ι 𝔅) (G l) ≠ 0) : SameOrbit z u := by sorry
