-- Prove2me | Theorems.Thm_GlobalTheory_SymSupportP_supportAt
-- name    : GlobalTheory.SymSupportP.supportAt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:29:47.10373+00:00
-- url     : https://prove2.me/theorems/7002833e-15a2-5288-87ca-cb28583e6506
-- title:
--   Sym Support P: support At
-- statement:
--   The Sym Support P construction uses the support At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainSupportAtOfPattern.lean#L91-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainSupportAtOfPattern.lean#L91-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRootExchangeParabolicMulPrincipalCongruencStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainSupportAtOfPattern
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymSupport
noncomputable section
open GlobalTheory GlobalTheory.SymSupportP
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SymSupportP.supportAt (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t) :
    S.SupportAt t := by sorry
