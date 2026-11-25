-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SymmetricPatternGroup_psiZero_residue
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup.psiZero_residue
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:58.62693+00:00
-- url     : https://prove2.me/theorems/c98296d8-0b6e-4d18-94e6-3978335f4977
-- title:
--   Symmetric Pattern Group: psi Zero residue
-- statement:
--   The Symmetric Pattern Group construction uses the psi Zero residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelEisenstein/SymmetricPatternGroup.lean#L186-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelEisenstein/SymmetricPatternGroup.lean#L186-L188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup.psiZero_residue {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) (u : 𝒪[k]) :
    psiZero hψ hϖ (IsLocalRing.residue 𝒪[k] u) = ψ ((u : k) / ϖ) := by sorry
