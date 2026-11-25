-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_isPerfectoidField_of_isAlgClosed_of_normedAlgebra
-- name    : GroundTheory.PAdicHodge.isPerfectoidField_of_isAlgClosed_of_normedAlgebra
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:40:18.395101+00:00
-- url     : https://prove2.me/theorems/207e90c3-0dea-4232-b8cc-1144df1e107c
-- title:
--   PAdic Hodge: is Perfectoid Field of is Alg Closed of normed Algebra
-- statement:
--   The PAdic Hodge construction uses the is Perfectoid Field of is Alg Closed of normed Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltEquiv.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltEquiv.lean#L57-L61

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Definitions.Def_GroundTheory_PAdicHodge_CompletedAlgClosure
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCharP
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
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
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
variable (K C p)
include K

theorem GroundTheory.PAdicHodge.isPerfectoidField_of_isAlgClosed_of_normedAlgebra [CompleteSpace C] :
    IsPerfectoidField C p := by sorry
