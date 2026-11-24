-- Prove2me | Theorems.Thm_GlobalTheory_CollapseCompare_exists_average
-- name    : GlobalTheory.CollapseCompare.exists_average
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:19:00.876184+00:00
-- url     : https://prove2.me/theorems/07043f8c-0842-46da-b22e-8d07429b9f64
-- title:
--   Collapse Compare: exists average
-- statement:
--   The Collapse Compare construction uses the exists average property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L23-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CoreIffCollapsesWith.lean#L23-L52

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
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_exists_average

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

theorem GlobalTheory.CollapseCompare.exists_average (ρ : Representation ℂ G V) (hρ : IsSmoothRep ρ) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) :
    ∃ e : V →ₗ[ℂ] V, (∀ g ∈ K, ∀ w, e (ρ g w) = e w) ∧ (∀ w, (∀ g ∈ K, ρ g w = w) → e w = w) ∧
      ∀ j : V →ₗ[ℂ] V, (∀ g w, j (ρ g w) = ρ g (j w)) → ∀ w, j (e w) = e (j w) := by sorry
