-- Prove2me | Theorems.Thm_GroundTheory_LocalField_quotient_mk_sum
-- name    : GroundTheory.LocalField.quotient_mk_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:10:53.639319+00:00
-- url     : https://prove2.me/theorems/3221f5c4-fcc3-4b97-af68-e3e3f3ac2e75
-- title:
--   Local Field: quotient mk sum
-- statement:
--   The Local Field construction uses the quotient mk sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L262-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L262-L264

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [ValuativeExtension K L]
  [FiniteDimensional K L]

theorem GroundTheory.LocalField.quotient_mk_sum {N : AddSubgroup L} {ι : Type*} [Fintype ι] (g : ι → L) :
    ∑ i, (g i : L ⧸ N) = ((∑ i, g i : L) : L ⧸ N) := by sorry
