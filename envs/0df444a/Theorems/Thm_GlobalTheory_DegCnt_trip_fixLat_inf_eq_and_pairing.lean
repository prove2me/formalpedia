-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_trip_fixLat_inf_eq_and_pairing
-- name    : GlobalTheory.DegCnt.trip_fixLat_inf_eq_and_pairing
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:21.059228+00:00
-- url     : https://prove2.me/theorems/28122ad3-0a72-4ba4-a005-2f1b5443bf38
-- title:
--   Deg Cnt: trip fix Lat inf eq and pairing
-- statement:
--   The Deg Cnt construction uses the trip fix Lat inf eq and pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FixedLatticeInfEqAndPairingOfIsometry.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FixedLatticeInfEqAndPairingOfIsometry.lean#L11-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FixedLatticeInfEqAndPairingOfIsometry
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
open GlobalTheory GlobalTheory.DegCnt

theorem GlobalTheory.DegCnt.trip_fixLat_inf_eq_and_pairing : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), ∀ p ∈ Trip H g L₀ j x x', fixLat p.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) = fixLat p.2.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) ∧ ∀ y ∈ fixLat p.1.2, ∀ y' ∈ fixLat p.2.1.2, ∃ t : 𝓞 K, H.B y (y' - p.2.2 y') = (g : K) * (t : K) := by sorry
