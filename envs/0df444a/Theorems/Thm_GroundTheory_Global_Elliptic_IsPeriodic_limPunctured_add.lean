-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_limPunctured_add
-- name    : GroundTheory.Global.Elliptic.IsPeriodic.limPunctured_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:19.47329+00:00
-- url     : https://prove2.me/theorems/8081efa3-a499-424b-bbfb-8ad85a1d1494
-- title:
--   Is Periodic: lim Punctured add
-- statement:
--   The Is Periodic construction uses the lim Punctured add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticConstant.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticConstant.lean#L45-L61

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℂ E]
variable {L : PeriodPair}

theorem GroundTheory.Global.Elliptic.IsPeriodic.limPunctured_add {f : ℂ → E} (hp : IsPeriodic L f) {z l : ℂ}
    (hl : l ∈ L.lattice) (hf : MeromorphicAt f z) (ho : 0 ≤ meromorphicOrderAt f z) :
    limPunctured f (z + l) = limPunctured f z := by sorry
