-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_exists_measure_compl_modulusSet_le
-- name    : MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:56.748984+00:00
-- url     : https://prove2.me/theorems/a7afad21-ba43-4db5-98e6-9061f2c92bfb
-- title:
--   MarkovProcess: exists_measure_compl_modulusSet_le
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicChaining_a582e42e
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicPathChaining_e74fe8f3
import Definitions.Def_MarkovProcess_V3H_Continuity_PathModulus_4f3af818
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.EMetricSpace.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A quantitative modulus of continuity from a Kolmogorov moment bound

The Kolmogorov--Chentsov argument is usually stated as an almost-sure Hölder property of a
continuous modification.  This file records the *quantitative* form that a tightness argument
needs: for a probability law on continuous paths whose coordinate process satisfies the
Kolmogorov moment condition with exponents `p`, `q` and constant `M`, the mass of the paths that
oscillate by more than `r` at scale `delta` on `[0, T]` is at most `eps`, once `delta` is small
enough --- and the threshold `delta` depends only on `p`, `q`, `M`, the Hölder exponent, `T`,
`r` and `eps`, not on the law.  This uniformity is the whole point: it is what makes the estimate
usable simultaneously at every starting point of a Markov process.

Main results:

* `MarkovProcess.ContinuousPath.modulusSet`, the closed set of paths whose oscillation over
  `[0, T]` at scale `delta` is at most `r`, with `isClosed_modulusSet` and
  `measurableSet_modulusSet`;
* `MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le`, the quantitative estimate,
  uniform over all laws obeying one and the same moment bound.

Nothing here constructs a law, asserts a Hölder exponent for individual paths, or claims
tightness; tightness is assembled from this estimate elsewhere.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoEMetricSpace alpha]









end ContinuousPath

section Estimate

variable {alpha : Type*} [PseudoEMetricSpace alpha]



















end Estimate

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# A quantitative modulus of continuity from a Kolmogorov moment bound

The Kolmogorov--Chentsov argument is usually stated as an almost-sure Hölder property of a
continuous modification.  This file records the *quantitative* form that a tightness argument
needs: for a probability law on continuous paths whose coordinate process satisfies the
Kolmogorov moment condition with exponents `p`, `q` and constant `M`, the mass of the paths that
oscillate by more than `r` at scale `delta` on `[0, T]` is at most `eps`, once `delta` is small
enough --- and the threshold `delta` depends only on `p`, `q`, `M`, the Hölder exponent, `T`,
`r` and `eps`, not on the law.  This uniformity is the whole point: it is what makes the estimate
usable simultaneously at every starting point of a Markov process.

Main results:

* `MarkovProcess.ContinuousPath.modulusSet`, the closed set of paths whose oscillation over
  `[0, T]` at scale `delta` is at most `r`, with `isClosed_modulusSet` and
  `measurableSet_modulusSet`;
* `MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le`, the quantitative estimate,
  uniform over all laws obeying one and the same moment bound.

Nothing here constructs a law, asserts a Hölder exponent for individual paths, or claims
tightness; tightness is assembled from this estimate elsewhere.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal




variable {alpha : Type*} [PseudoEMetricSpace alpha]

















open MarkovProcess in

theorem MarkovProcess.ContinuousPath.exists_measure_compl_modulusSet_le {p q : ℝ} {M : ℝ≥0} {gamma : ℝ}
    (hp : 0 < p) (hgamma : 0 < gamma) (hgammaq : gamma < (q - 1) / p) (T : ℝ≥0) {r : ℝ≥0∞}
    (hr : 0 < r) {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ delta : ℝ≥0∞, 0 < delta ∧
      ∀ mu : Measure (ContinuousPath alpha),
        IsKolmogorovProcess (fun (t : ℝ≥0) (omega : ContinuousPath alpha) ↦ omega t) mu p q M →
          mu (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps := by sorry
