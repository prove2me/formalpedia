-- Prove2me | Theorems.Thm_GlobalTheory_CollapseCompare_exists_equivariant
-- name    : GlobalTheory.CollapseCompare.exists_equivariant
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:19:50.900921+00:00
-- url     : https://prove2.me/theorems/ea84d148-801e-42c4-bd8c-a545a9fcad0c
-- title:
--   Collapse Compare: exists equivariant
-- statement:
--   The Collapse Compare construction uses the exists equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L54-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L54-L77

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
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CollapseCompare.exists_equivariant {H : Type} [Group H] (ρ : Representation ℂ G V) (hρ : IsSmoothRep ρ)
    (π : Representation ℂ H V) (hcomm : ∀ g h w, π h (ρ g w) = ρ g (π h w)) (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : Module ℂ P) (π' : Representation ℂ G P) (θ : P →ₗ[ℂ] V →ₗ[ℂ] V) (φ : P),
      IsSmoothRep π' ∧ (∀ g h T w, θ (π' g T) (ρ g (π h w)) = π h (θ T w)) ∧
        ∀ w, (∀ g ∈ K, ρ g w = w) → θ φ w = w := by sorry
