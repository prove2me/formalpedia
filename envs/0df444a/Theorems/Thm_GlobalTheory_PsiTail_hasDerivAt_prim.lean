-- Prove2me | Theorems.Thm_GlobalTheory_PsiTail_hasDerivAt_prim
-- name    : GlobalTheory.PsiTail.hasDerivAt_prim
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:09.189207+00:00
-- url     : https://prove2.me/theorems/c8873b3a-5a28-41cb-80d2-41e3995b68e2
-- title:
--   Psi Tail: has Deriv At prim
-- statement:
--   The Psi Tail construction uses the has Deriv At prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/Gl2L2Integrality.lean#L89-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/Gl2L2Integrality.lean#L89-L111

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2Integrality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.PsiTail
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

theorem GlobalTheory.PsiTail.hasDerivAt_prim (Q E u : ℝ) (hQ : 0 < Q) (hu : 1 < u) :
    HasDerivAt (fun t : ℝ => -(t ^ (-(1 : ℝ) / 400) *
        (400 * Real.log (t * Q) ^ 2 + 320000 * Real.log (t * Q) + 128000000) + E / Real.log t))
      ((u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) / u) u := by sorry
