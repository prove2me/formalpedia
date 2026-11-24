-- Prove2me | Theorems.Thm_GlobalTheory_PairOp_smul_ofDual
-- name    : GlobalTheory.PairOp.smul_ofDual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:52.962071+00:00
-- url     : https://prove2.me/theorems/ce5b6955-8f0f-4f52-8384-bc84c60c99e1
-- title:
--   Pair Op: smul of Dual
-- statement:
--   The Pair Op construction uses the smul of Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PairOperatorStatement.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.PairOp.smul_ofDual (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (c : 𝓀[k]ˣ)
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) :
    c • ofDual L f = ofDual L ⟨(c : 𝓀[k]) • f.1, smul_ne_zero c.ne_zero f.2⟩ := by sorry
