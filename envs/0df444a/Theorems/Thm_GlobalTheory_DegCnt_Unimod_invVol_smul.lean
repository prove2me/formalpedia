-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_Unimod_invVol_smul
-- name    : GlobalTheory.DegCnt.Unimod.invVol_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:03.275646+00:00
-- url     : https://prove2.me/theorems/72d4a654-ce8c-45a1-9cf1-3d62ce6fded9
-- title:
--   Unimod: inv Vol smul
-- statement:
--   The Unimod construction uses the inv Vol smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexNeZero.lean#L169-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexNeZero.lean#L169-L211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexNeZero
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Unimod
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.Unimod.invVol_smul : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (n : ℕ), (∀ s ∈ G, ((s : V →ₗ[K] V) - 1) ^ n = 0) → ∀ Λ Λ' : Submodule (𝓞 K) V, Submodule.IsLattice K Λ → Submodule.IsLattice K Λ' → (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ).relIndex (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') ≠ 0 ∧ ∀ s ∈ G, GlobalTheory.HL.invVol (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) (s • Λ)) = GlobalTheory.HL.invVol (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ) := by sorry
