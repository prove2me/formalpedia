-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_tsum_rep_mul
-- name    : GlobalTheory.CompanionTheory.RgEis.tsum_rep_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:26.882653+00:00
-- url     : https://prove2.me/theorems/355cc750-6740-40f4-a7e8-59ad544a9ec6
-- title:
--   Rg Eis: tsum rep mul
-- statement:
--   The Rg Eis construction uses the tsum rep mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L41-L51

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis

theorem GlobalTheory.CompanionTheory.RgEis.tsum_rep_mul {G : Type} [Group G] {X : Type} [AddCommMonoid X] [TopologicalSpace X]
    {P Γ : Subgroup G} (F : G → X) (hF : ∀ δ ∈ Γ, δ ∈ P → ∀ x, F (δ * x) = F x) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    ∑' q : Cos P Γ, F (rep q * (γ * g)) = ∑' q : Cos P Γ, F (rep q * g) := by sorry
