-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_ResProj_cross_mem
-- name    : GlobalTheory.CompanionTheory.Ar.Giv.ResProj.cross_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:22:34.680661+00:00
-- url     : https://prove2.me/theorems/753e5119-29a3-4cd7-b142-93e1fc9cddfd
-- title:
--   Res Proj: cross mem
-- statement:
--   The Res Proj construction uses the cross mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean#L84-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean#L84-L107

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
variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ _ : Unit, Fin M) → Ω) {G : Fin M → MRing ι} {g : K → ℕ}

theorem GlobalTheory.CompanionTheory.Ar.Giv.ResProj.cross_mem (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) (i j : Fin M) :
    (X (⟨Sum.inr (), i⟩ : Σ k, joinIdx ι 𝔅 k) : MRing (joinIdx ι 𝔅)) * rename (joinInl ι 𝔅) (G j) -
      X (⟨Sum.inr (), j⟩ : Σ k, joinIdx ι 𝔅 k) * rename (joinInl ι 𝔅) (G i) ∈ mCoordIdeal (joinVec y y') := by sorry
