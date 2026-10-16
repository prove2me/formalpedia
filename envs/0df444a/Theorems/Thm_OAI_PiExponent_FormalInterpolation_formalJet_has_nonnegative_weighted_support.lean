-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_has_nonnegative_weighted_support
-- name    : OAI.PiExponent.FormalInterpolation.formalJet_has_nonnegative_weighted_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:37:42.937031+00:00
-- url     : https://prove2.me/theorems/810b2b60-df33-4fc2-86bb-416e0950e168
-- title:
--   Nonnegative weighted support of formal logarithmic jets
-- statement:
--   Under nonnegative variable weights and the stated truncation bounds, every polynomial's formal logarithmic jet has no nonzero coefficient of negative weighted degree.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, cited by the parent target.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.formalJet_has_nonnegative_weighted_support
    {m : Nat} (c : Fin m -> Complex) (T : Fin m -> Nat)
    (v : Fin (m + 1) -> Real)
    (hv : forall i, 0 <= v i)
    (hT : forall i, v i.succ <= (T i : Real) * v 0)
    (P : MvPolynomial (Fin (m + 1)) Complex) :
    FormalInterpolation.hasWeightedSupport v 0
      (FormalInterpolation.formalJet c P) := by sorry
