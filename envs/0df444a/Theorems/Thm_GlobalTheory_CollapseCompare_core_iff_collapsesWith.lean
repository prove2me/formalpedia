-- Prove2me | Theorems.Thm_GlobalTheory_CollapseCompare_core_iff_collapsesWith
-- name    : GlobalTheory.CollapseCompare.core_iff_collapsesWith
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:22.621713+00:00
-- url     : https://prove2.me/theorems/e0bc694f-cc1c-4efb-bbf8-aa1733223eea
-- title:
--   Collapse Compare: core iff collapses With
-- statement:
--   The Collapse Compare construction uses the core iff collapses With property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L545-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L545-L552

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

theorem GlobalTheory.CollapseCompare.core_iff_collapsesWith {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c : ℕ} (hc : 1 ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k))
    (μG : Measure (GL (n ⊕ Fin c) k)) {J : Subgroup (GL (n ⊕ Fin c) k)} (hJ : IsOpen (J : Set (GL (n ⊕ Fin c) k)))
    (bas : GL (n ⊕ Fin c) k) (ψ : AddChar k Circle) {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ)) (lam : J →* ℂˣ)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (hΦ : HasTargetType μ J lam Φ.1) (κ : ℝ) :
    Core ν μX μG J bas ψ μ lam Φ.1 κ ↔ CollapsesWith ν μX μG J bas ψ μ lam Φ κ := by sorry
