-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_FrameCramer_cramer
-- name    : GlobalTheory.DegCnt.FrameCramer.cramer
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:27:54.596849+00:00
-- url     : https://prove2.me/theorems/7253d509-8d0c-4ebc-9c24-16a1ca20aac7
-- title:
--   Frame Cramer: cramer
-- statement:
--   The Frame Cramer construction uses the cramer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean#L226-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean#L226-L252

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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FrameCramer
open Matrix
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open GlobalTheory.DegCnt.IdealPow

theorem GlobalTheory.DegCnt.FrameCramer.cramer (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)) {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥)
    (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K))
    (hF : ∀ a : Fin r, lead F Λ a.castSucc = ipow 𝔡 (-((r : ℤ) - a.val)))
    (hF' : ∀ a : Fin r, lead F' Λ a.castSucc = ipow 𝔡 (-((r : ℤ) - a.val))) {l : ℕ} (hl : l ≤ r) {u : K}
    (hu : u ∈ ipow 𝔡 (-(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)))) :
    u * Dl F F' l (hl.trans (Nat.le_succ r)) ∈ (1 : Submodule (𝓞 K) K) ∧
    ∀ x ∈ F.Xa l, (∀ p ∈ Λ, p ∈ F'.Xa l → H.B x p ∈ (1 : Submodule (𝓞 K) K)) →
      (u * Dl F F' l (hl.trans (Nat.le_succ r))) • x ∈ Λ := by sorry
