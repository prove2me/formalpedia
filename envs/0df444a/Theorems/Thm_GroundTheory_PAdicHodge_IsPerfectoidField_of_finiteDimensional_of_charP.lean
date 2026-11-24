-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_of_finiteDimensional_of_charP
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.of_finiteDimensional_of_charP
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:26.73213+00:00
-- url     : https://prove2.me/theorems/d7b3c040-4746-4d5c-b6ab-ddfe8d5c7a6a
-- title:
--   Is Perfectoid Field: of finite Dimensional of char P
-- statement:
--   The Is Perfectoid Field construction uses the of finite Dimensional of char P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCharP.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidCharP.lean#L40-L52

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCharP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.of_finiteDimensional_of_charP (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] [CharP K p]
    (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] : IsPerfectoidField L p := by sorry
