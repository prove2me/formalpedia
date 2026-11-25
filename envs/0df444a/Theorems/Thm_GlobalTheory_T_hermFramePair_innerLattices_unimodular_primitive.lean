-- Prove2me | Theorems.Thm_GlobalTheory_T_hermFramePair_innerLattices_unimodular_primitive
-- name    : GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:40:24.917641+00:00
-- url     : https://prove2.me/theorems/bdd42dfb-c118-446a-8d31-ed31c60d0e12
-- title:
--   T: herm Frame Pair inner Lattices unimodular primitive
-- statement:
--   The T construction uses the herm Frame Pair inner Lattices unimodular primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairInnerLatticesUnimodularPrimitiveStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairInnerLatticesUnimodularPrimitiveStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitive
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitiveStatement
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

theorem GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → IsUnimodMod H (latL N.F N.F' Λ) (uPerp N.F N.F') (II N.F N.F') ∧ IsUnimodMod H (latL N.F' N.F Λ) (uPerp N.F N.F') (II N.F N.F') ∧ (∀ t : K, t • N.F.z ∈ latL N.F N.F' Λ ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧ (∀ t : K, t • N.F'.z ∈ latL N.F' N.F Λ ↔ t ∈ (1 : Submodule (𝓞 K) K)) ∧ Submodule.IsLattice K (N.Ref (latL N.F N.F' Λ)) ∧ N.Ref (latL N.F N.F' Λ) ⊓ rs (𝓞 K) (V0 N.F N.F') = N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') := by sorry
