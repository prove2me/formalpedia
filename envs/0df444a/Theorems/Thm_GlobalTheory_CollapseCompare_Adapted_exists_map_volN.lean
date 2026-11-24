-- Prove2me | Theorems.Thm_GlobalTheory_CollapseCompare_Adapted_exists_map_volN
-- name    : GlobalTheory.CollapseCompare.Adapted.exists_map_volN
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:17.312806+00:00
-- url     : https://prove2.me/theorems/dd5774b5-0a50-406f-be00-bf8ba9d0023e
-- title:
--   Adapted: exists map vol N
-- statement:
--   The Adapted construction uses the exists map vol N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L331-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L331-L356

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.CollapseCompare.Adapted.exists_map_volN {t : GL (n ⊕ Fin c) k} (ht : Adapted t) (ν ν₀ : Measure k) [ν.IsAddHaarMeasure]
    [ν₀.IsAddHaarMeasure] :
    ∃ r : ℝ≥0, r ≠ 0 ∧ (∀ F : GL (n ⊕ Fin c) k → ℂ,
        ∫ u : N k n c 1, F (t * u * t⁻¹) ∂(volN ν₀ n c 1) = (r : ℝ) • ∫ u : N k n c 1, F u ∂(volN ν n c 1)) ∧
      ∀ S S₀ : Subgroup (GL (n ⊕ Fin c) k), (∀ u ∈ N k n c 1, u ∈ S₀ ↔ t * u * t⁻¹ ∈ S) →
        volN ν₀ n c 1 (S₀.subgroupOf (N k n c 1)) = r * volN ν n c 1 (S.subgroupOf (N k n c 1)) := by sorry
