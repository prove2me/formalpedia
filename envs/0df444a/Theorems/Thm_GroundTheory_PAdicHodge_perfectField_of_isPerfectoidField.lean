-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_perfectField_of_isPerfectoidField
-- name    : GroundTheory.PAdicHodge.perfectField_of_isPerfectoidField
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:14.52673+00:00
-- url     : https://prove2.me/theorems/a6cd36c4-ae3a-410e-bfe3-023c307f543a
-- title:
--   PAdic Hodge: perfect Field of is Perfectoid Field
-- statement:
--   The PAdic Hodge construction uses the perfect Field of is Perfectoid Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApprox.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApprox.lean#L14-L37

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
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
open Polynomial

theorem GroundTheory.PAdicHodge.perfectField_of_isPerfectoidField (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] : PerfectField K := by sorry
