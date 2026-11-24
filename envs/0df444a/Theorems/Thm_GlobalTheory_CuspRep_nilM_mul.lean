-- Prove2me | Theorems.Thm_GlobalTheory_CuspRep_nilM_mul
-- name    : GlobalTheory.CuspRep.nilM_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:01.621223+00:00
-- url     : https://prove2.me/theorems/f521a11a-8f04-495a-8ebb-065ca66a08d9
-- title:
--   Cusp Rep: nil M mul
-- statement:
--   The Cusp Rep construction uses the nil M mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/IsOpenStabOfMemNhds.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/IsOpenStabOfMemNhds.lean#L27-L33

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsOpenStabilizer
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_IsOpenStabOfMemNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CuspRep
variable {a : ℕ} {R : Type} [CommRing R]

theorem GlobalTheory.CuspRep.nilM_mul {r : ℕ} (x y : BlockIx a r → R) : nilM x * nilM y = 0 := by sorry
