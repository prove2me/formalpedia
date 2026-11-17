-- Prove2me | Theorems.Thm_Kyprianou_Ch07_driftingOscillatingLevyMeasureCriterion
-- name    : Kyprianou.Ch07.driftingOscillatingLevyMeasureCriterion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:46:46.135187+00:00
-- url     : https://prove2.me/theorems/0d77295f-b822-4c30-b2cc-d8cab3a48905
-- title:
--   Theorem 7.2: drift trichotomy from extended mean and Lévy jump tails
-- statement:
--   For a real Lévy process with its actual Lévy–Khintchine measure Π: (i) a well-defined extended strictly negative mean E X_1, or an undefined mean with the large-positive-jump divided-by-integrated-negative-tail test finite, implies drift to minus infinity; (ii) the dual positive mean/negative-jump integral implies drift to plus infinity; (iii) a defined zero mean, or an undefined mean with both ratio tests divergent, implies unbounded positive and negative oscillation almost surely. Extended means are encoded by their positive and negative nonnegative integrals, preventing spurious totalised expectations. The zero-mean oscillation conclusion excludes the identically-zero Lévy law, a mathematical exception absent from the printed theorem (p.183). The extended-mean and tail alternatives remain unchanged.
-- source:
--   Kyprianou (2006), first edition, Theorem 7.2(i)–(iii), printed p.183, Windows Ky.pdf sheet 97 (original single-page PDF p.192). The author omits the proof.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Theorem 7.2(i)-(iii): full trichotomy determined by the
extended mean of X_1 or, when undefined, the large-jump ratio tests.
The zero-mean oscillation clause excludes the identically-zero law,
an unstated exception in the printed source. -/
theorem driftingOscillatingLevyMeasureCriterion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi) :
    (((positiveMeanPart P X < negativeMeanPart P X) ∨
       (HasUndefinedLevyMean P X ∧ negativeDriftTailTest Pi < ⊤) →
       DriftsToNegInfinity P X) ∧
     ((negativeMeanPart P X < positiveMeanPart P X) ∨
       (HasUndefinedLevyMean P X ∧ positiveDriftTailTest Pi < ⊤) →
       DriftsToPosInfinity P X) ∧
     (((positiveMeanPart P X = negativeMeanPart P X ∧
        positiveMeanPart P X < ⊤) ∨
       (HasUndefinedLevyMean P X ∧
        negativeDriftTailTest Pi = ⊤ ∧
        positiveDriftTailTest Pi = ⊤)) →
       IsNontrivialLevyProcess P X →
       OscillatesAtInfinity P X)) := by
  sorry

end Kyprianou.Ch07
