-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logCoord_aeval_on_fibre
-- name    : OAI.PiExponent.FormalInterpolation.logCoord_aeval_on_fibre
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:05:57.963383+00:00
-- url     : https://prove2.me/theorems/0f399b84-efe5-4467-914c-4f24dc051d75
-- title:
--   Evaluate the logarithmic coordinate on the fibre
-- statement:
--   On the fibre where the zeroth coordinate is 1, evaluating the logarithmic coordinate removes the truncated logarithm term and leaves the translated coordinate.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.FieldTheory.IsAlgClosed.Basic

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logCoord_aeval_on_fibre
    {m : Nat} (c : Fin m → Complex)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1) (i : Fin m) :
    MvPolynomial.aeval x
      (logarithmicCoordinate c (fun _ => e 0) i.succ) =
      x i.succ - algebraMap Complex E (c i) := by sorry
