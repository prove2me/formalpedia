-- Prove2me | Theorems.Thm_GlobalTheory_LocalNormBound_local_bound
-- name    : GlobalTheory.LocalNormBound.local_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:38.33967+00:00
-- url     : https://prove2.me/theorems/660d0d5d-f31e-4253-a075-d4818ce621ee
-- title:
--   Local Norm Bound: local bound
-- statement:
--   The Local Norm Bound construction uses the local bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImportsTer.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImportsTer.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Filter Topology
open GlobalTheory GlobalTheory.LocalNormBound

theorem GlobalTheory.LocalNormBound.local_bound (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (W : Set (v.adicCompletion F)) (hW : W ∈ 𝓝 (0 : v.adicCompletion F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ v.adicCompletionIntegers F, N • x ∈ W := by sorry
