-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_eq_of_mk_eq
-- name    : GroundTheory.Global.Elliptic.IsPeriodic.eq_of_mk_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:19.151056+00:00
-- url     : https://prove2.me/theorems/5aac816a-8a2a-47d6-84ed-230cf7cf829f
-- title:
--   Is Periodic: eq of mk eq
-- statement:
--   The Is Periodic construction uses the eq of mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticFunctions.lean#L48-L51

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
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
variable (L : PeriodPair)
variable {L}

theorem GroundTheory.Global.Elliptic.IsPeriodic.eq_of_mk_eq {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) {z w : ℂ}
    (h : Torus.mk L z = Torus.mk L w) : f z = f w := by sorry
