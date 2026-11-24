-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Giv_anLogRes_of_embedded_join
-- name    : GlobalTheory.CompanionTheory.Ar.Giv.anLogRes_of_embedded_join
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:19:41.069508+00:00
-- url     : https://prove2.me/theorems/4eb89dbc-8cd3-4119-9de6-2ff3b5e491ad
-- title:
--   Giv: an Log Res of embedded join
-- statement:
--   The Giv construction uses the an Log Res of embedded join property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean#L353-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoin.lean#L353-L421

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
open ResProj

theorem GlobalTheory.CompanionTheory.Ar.Giv.anLogRes_of_embedded_join : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))) (R : AnLogRes (mCoordIdeal (joinVec y y')) J e) (γ : MRing ι) (c : K → ℕ), IsEmbedded R.A (mCoordIdeal (joinVec y y')) R.U R.lift → (∃ i, y' ⟨(), i⟩ ≠ 0) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsMultiHomog γ c → γ ∉ mCoordIdeal y → (∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) γ) = 0 → z ∈ mcPts J) → (∀ z ∈ mcPts (mCoordIdeal y), evC z γ ≠ 0 → ∃ (G : Fin M → MRing ι) (g : K → ℕ), (∀ i, IsMultiHomog (G i) g) ∧ (∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) ∧ ∃ i, evC z (G i) ≠ 0) → Nonempty (AnLogRes (mCoordIdeal y) (Ideal.span {γ}) e) := by sorry
