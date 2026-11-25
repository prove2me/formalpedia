-- Prove2me | Theorems.Thm_GlobalTheory_UnipStab_common_unipotent_stabiliser
-- name    : GlobalTheory.UnipStab.common_unipotent_stabiliser
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:02:15.206601+00:00
-- url     : https://prove2.me/theorems/18fd4a3a-9aa4-56cc-b27e-28a495a00ef7
-- title:
--   Unip Stab: common unipotent stabiliser
-- statement:
--   The Unip Stab construction uses the common unipotent stabiliser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairCommonUnipotentStabiliserSummary.lean#L484-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairCommonUnipotentStabiliserSummary.lean#L484-L491

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
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
open GlobalTheory GlobalTheory.UnipStab
open NumberField
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.UnipStab.common_unipotent_stabiliser : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : _root_.GlobalTheory.DegCnt.NF H r), (∀ s : V ≃ₗ[K] V, s ∈ N.R ↔ N.F.InN (s : V →ₗ[K] V) ∧ N.F'.InN (s : V →ₗ[K] V)) ∧ (∀ s ∈ N.R, ∀ y ∈ _root_.GlobalTheory.HermLat.uPerp N.F N.F', s y - y ∈ _root_.Formalism.HermitianLatticeCounting.S6.II N.F N.F') ∧ (∀ s ∈ N.R, ∀ t ∈ N.R1, s * t * s⁻¹ ∈ N.R1) ∧ (∀ s ∈ N.R, ∀ t ∈ N.ZI, s * t * s⁻¹ ∈ N.ZI) ∧ ∀ s ∈ N.R, ((s : V →ₗ[K] V) - 1) ^ (2 * r + 1) = 0 := by sorry
