-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_transvection_mul_eq_diagonal_update
-- name    : GroundTheory.Automorphic.transvection_mul_eq_diagonal_update
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:21.524603+00:00
-- url     : https://prove2.me/theorems/242c7fbe-44e0-4fa1-9093-7f2a5056e4a9
-- title:
--   Automorphic: transvection mul eq diagonal update
-- statement:
--   The Automorphic construction uses the transvection mul eq diagonal update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L60-L71

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (n) (R : Type*) [CommRing R]
variable {n R}

theorem GroundTheory.Automorphic.transvection_mul_eq_diagonal_update (i j : n) (hij : i ≠ j) (u : Rˣ) :
    transvection i j (u : R) * transvection j i (-(↑u⁻¹ : R)) * transvection i j (u : R) *
      transvection i j (-1) * transvection j i 1 * transvection i j (-1) =
      diagonal (Function.update (Function.update (1 : n → R) i u) j (↑u⁻¹ : R)) := by sorry
