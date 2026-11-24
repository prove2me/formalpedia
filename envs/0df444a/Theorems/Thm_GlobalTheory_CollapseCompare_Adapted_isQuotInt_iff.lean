-- Prove2me | Theorems.Thm_GlobalTheory_CollapseCompare_Adapted_isQuotInt_iff
-- name    : GlobalTheory.CollapseCompare.Adapted.isQuotInt_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:19:34.568948+00:00
-- url     : https://prove2.me/theorems/1cd4cbee-8c62-4d0e-a6df-2deb799fc821
-- title:
--   Adapted: is Quot Int iff
-- statement:
--   The Adapted construction uses the is Quot Int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L374-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L374-L407

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

theorem GlobalTheory.CollapseCompare.Adapted.isQuotInt_iff {t : GL (n ⊕ Fin c) k} (ht : Adapted t) {ν ν₀ : Measure k} {r : ℝ≥0} (hr : r ≠ 0)
    (H : ∀ F : GL (n ⊕ Fin c) k → ℂ,
        ∫ u : N k n c 1, F (t * u * t⁻¹) ∂(volN ν₀ n c 1) = (r : ℝ) • ∫ u : N k n c 1, F u ∂(volN ν n c 1))
    (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)) (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ) :
    IsQuotInt ν₀ (r⁻¹ • μX) (μG.map (cjG t).symm) 1 (fun h => f (cjG t h)) z ↔ IsQuotInt ν μX μG 1 f z := by sorry
