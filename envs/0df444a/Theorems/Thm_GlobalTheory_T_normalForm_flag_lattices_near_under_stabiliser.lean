-- Prove2me | Theorems.Thm_GlobalTheory_T_normalForm_flag_lattices_near_under_stabiliser
-- name    : GlobalTheory.T.normalForm_flag_lattices_near_under_stabiliser
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:50:02.31761+00:00
-- url     : https://prove2.me/theorems/e6f6dec9-4f78-595e-b468-a45b3a1d97cf
-- title:
--   T: normal Form flag lattices near under stabiliser
-- statement:
--   The T construction uses the normal Form flag lattices near under stabiliser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliserStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormalFormFlagLatticesNearUnderStabiliserStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliserStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.normalForm_flag_lattices_near_under_stabiliser : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∃ s ∈ N.Rs, (∀ y ∈ II N.F N.F' ⊔ Submodule.span K {N.F.z} ⊔ N.Ist, s y = y) ∧ ∀ Λ' : Submodule (𝓞 K) V, Λ' = s • Λ → 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ Λ' ∧ 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ Λ' ∧ 𝔠 ^ (2 * r + 2) • (Λ' ⊓ rs (𝓞 K) (N.F.Xa N.j)) ≤ N.P0 ∧ 𝔠 ^ (2 * r + 2) • (Λ' ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ≤ N.P0 := by sorry
