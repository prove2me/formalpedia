-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_Monomial_monomial
-- name    : GlobalTheory.DegCnt.Monomial.monomial
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:27:47.456029+00:00
-- url     : https://prove2.me/theorems/1b37aafe-a7ad-42df-ad7c-1e7ca8b3290b
-- title:
--   Monomial: monomial
-- statement:
--   The Monomial construction uses the monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean#L279-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean#L279-L337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemOfForall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairingCramerOfLeadingCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Monomial
open GlobalTheory.DegCnt.IdealPow GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V}

theorem GlobalTheory.DegCnt.Monomial.monomial {ι : Type} [Fintype ι] (v : ι → V) (n : ι → ℤ) {𝔡 𝔠 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥)
    (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K))
    (h1 : ∀ i k, H.B (v i) (v k) ≠ 0 → ∀ γ ∈ 𝔠,
      (∀ u ∈ ipow 𝔡 (n i + n k), (γ : K) * u * H.B (v i) (v k) ∈ (1 : Submodule (𝓞 K) K)) ∧
      (∀ u ∈ ipow 𝔡 (-(n i + n k)), (γ : K) * u / H.B (v i) (v k) ∈ (1 : Submodule (𝓞 K) K)))
    (h2 : ∀ i, ∃ k, H.B (v i) (v k) ≠ 0 ∧ ∀ i', i' ≠ i → H.B (v i') (v k) = 0)
    (P : Submodule (𝓞 K) V) (hP : P = ⨆ i, line (ipow 𝔡 (n i)) (v i)) :
    𝔠 • dual H P ≤ P ∧ 𝔠 • P ≤ dual H P := by sorry
