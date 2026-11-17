-- Prove2me | Theorems.Thm_Kyprianou_Ch07_driftingOscillatingIntegralTrichotomy
-- name    : Kyprianou.Ch07.driftingOscillatingIntegralTrichotomy
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:44:06.793493+00:00
-- url     : https://prove2.me/theorems/b19f9427-4332-4378-b603-d7bbc9d19db8
-- title:
--   Theorem 7.1: integral trichotomy for drift and oscillation
-- statement:
--   Theorem 7.1 in all three parts. For every real-valued Lévy process, integrability of t^-1 times P(X_t≥0) over t≥1 implies drift to minus infinity almost surely, integrability of t^-1 times P(X_t≤0) implies drift to plus infinity almost surely, and divergence of both integrals implies pathwise oscillation with limsup=+infinity and liminf=-infinity almost surely. The source's weak sign inequalities and integral domains are retained. Mathematical exception omitted in the printed text (p.180): joint divergence implies oscillation when the Lévy law is nontrivial; the zero process has two divergent tests and does not oscillate.
-- source:
--   Kyprianou (2006), first edition, Theorem 7.1(i)–(iii), printed page 180, Windows Ky.pdf landscape sheet 95 (original single-page PDF p.189).

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Theorem 7.1, parts (i), (ii) and (iii).
Finiteness of the positive/negative time-sign integral gives the
corresponding almost-sure drift, and divergence of both means oscillation for nontrivial Lévy laws.
The printed source omits the zero-process exception. -/
theorem driftingOscillatingIntegralTrichotomy
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X) :
    ((nonnegativeSignIntegral P X < ⊤ →
      DriftsToNegInfinity P X) ∧
     (nonpositiveSignIntegral P X < ⊤ →
      DriftsToPosInfinity P X) ∧
     (nonnegativeSignIntegral P X = ⊤ →
      nonpositiveSignIntegral P X = ⊤ →
      IsNontrivialLevyProcess P X →
      OscillatesAtInfinity P X)) := by
  sorry

end Kyprianou.Ch07
