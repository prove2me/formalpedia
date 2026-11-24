-- Prove2me | Theorems.Thm_GlobalTheory_SuperCusp_val_le_one_of_mem_cong
-- name    : GlobalTheory.SuperCusp.val_le_one_of_mem_cong
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:24:17.815002+00:00
-- url     : https://prove2.me/theorems/cdf9ac78-9946-429a-9d40-5b659ae30284
-- title:
--   Super Cusp: val le one of mem cong
-- statement:
--   The Super Cusp construction uses the val le one of mem cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L105-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L105-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCuspidalOfIsSupercuspidal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
noncomputable section
open GlobalTheory GlobalTheory.SuperCusp

theorem GlobalTheory.SuperCusp.val_le_one_of_mem_cong {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {κ : GL n k}
    (hκ : κ ∈ CentralExponent.cong n (1 : (ValueGroupWithZero k)ˣ) le_rfl) (p q : n) :
    valuation k ((κ : Matrix n n k) p q) ≤ 1 := by sorry
