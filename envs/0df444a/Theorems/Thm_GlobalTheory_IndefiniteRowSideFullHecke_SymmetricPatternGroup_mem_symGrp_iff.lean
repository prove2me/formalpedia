-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SymmetricPatternGroup_mem_symGrp_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup.mem_symGrp_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:42.365672+00:00
-- url     : https://prove2.me/theorems/4422e3fc-e245-5780-a129-851b74df9c3b
-- title:
--   Symmetric Pattern Group: mem sym Grp iff
-- statement:
--   The Symmetric Pattern Group construction uses the mem sym Grp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelEisenstein/SymmetricPatternGroup.lean#L77-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelEisenstein/SymmetricPatternGroup.lean#L77-L112

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
variable (F : Type*) [Field F] [Finite F] (κ ρ : ℕ)
variable {F κ ρ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup.mem_symGrp_iff {g : GL (Fin κ ⊕ Fin (2 * ρ + 1)) F} :
    g ∈ symGrp F κ ρ ↔ ∃ n ∈ radN F κ ρ, ∃ u ∈ epsU F κ ρ, g = n * u := by sorry
