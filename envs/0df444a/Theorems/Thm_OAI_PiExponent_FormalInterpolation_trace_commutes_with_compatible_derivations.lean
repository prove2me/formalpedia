-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_trace_commutes_with_compatible_derivations
-- name    : OAI.PiExponent.FormalInterpolation.trace_commutes_with_compatible_derivations
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:23:22.887762+00:00
-- url     : https://prove2.me/theorems/783583a0-a6d5-451a-9183-65c42b35e752
-- title:
--   Field trace commutes with compatible derivations
-- statement:
--   Choose an L-basis b of E. Let A describe D on the basis and M(x) describe multiplication by x. Differentiating the multiplication identities gives M(Dx)=d(M(x))+A M(x)−M(x)A, with d applied entrywise. Taking matrix traces cancels the commutator and gives the claimed identity. The inspected declaration Algebra.trace_eq_matrix_trace connects this calculation to field trace. This child removes only trace compatibility; the candidate separately constructs the extended derivation. The argument works in every characteristic and needs neither separability nor algebraic closedness, provided compatible derivations are supplied. For degree one it reduces to their compatibility identity.

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Trace.Defs

theorem OAI.PiExponent.FormalInterpolation.trace_commutes_with_compatible_derivations
    (k L E : Type) [Field k] [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E]
    [IsScalarTower k L E] [FiniteDimensional L E]
    (d : Derivation k L L) (D : Derivation k E E)
    (hcompat : ∀ a : L, D (algebraMap L E a) = algebraMap L E (d a))
    (x : E) :
    d (Algebra.trace L E x) = Algebra.trace L E (D x) := by sorry
