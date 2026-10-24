-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_exists_test_near_of_relaxation_lt_408915f
-- name    : FunctionalInequalities.Energy.PreEnergy.exists_test_near_of_relaxation_lt_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:54.409881+00:00
-- url     : https://prove2.me/theorems/f0553606-b6ae-49f5-bf8d-6dfe668c592b
-- title:
--   Concrete Test Below A Strict Relaxed-Energy Bound
-- statement:
--   This is an approximation-selection lemma for sequential relaxation.
--
--   Let $X$ be a pseudometric space, let $P$ be a pre-energy on $X$, let $x\in X$, and let $B\in[0,\infty]$ be an `ENNReal` bound. Assume the relaxed energy is strictly below $B$:
--
--   $$
--   P.\operatorname{sequentialRelaxation}(x)<B.
--   $$
--
--   For every real radius $\varepsilon>0$, there exists a concrete test $f\in P.\operatorname{Test}$ such that
--
--   $$
--   \operatorname{dist}(P.\operatorname{toAmbient}(f),x)<\varepsilon
--   \quad\text{and}\quad
--   (P.\operatorname{energy}(f):\operatorname{ENNReal})<B.
--   $$
--
--   The Lean declaration is `exists_test_near_of_relaxation_lt`. The strict relaxed-energy hypothesis and strict energy conclusion are essential parts of the statement; it does not assert attainment of a minimum.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/Approximation.lean#L29-L45 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.Approximation`, declaration `FunctionalInequalities.Energy.PreEnergy.exists_test_near_of_relaxation_lt`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Sequences

noncomputable section
open Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
universe u
variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)

theorem FunctionalInequalities.Energy.PreEnergy.exists_test_near_of_relaxation_lt_408915f {x : X} {bound : ENNReal}
    (hbound : P.sequentialRelaxation x < bound) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : P.Test, dist (P.toAmbient f) x < ε ∧ (P.energy f : ENNReal) < bound := by sorry
