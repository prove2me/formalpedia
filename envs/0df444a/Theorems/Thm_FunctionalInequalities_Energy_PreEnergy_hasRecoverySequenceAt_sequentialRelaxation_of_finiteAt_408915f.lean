-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt_408915f
-- name    : FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:54.048875+00:00
-- url     : https://prove2.me/theorems/cbcdc748-8192-4a61-98ee-55707d78f402
-- title:
--   Recovery Sequence At A Finite Relaxed-Energy Point
-- statement:
--   This theorem gives a recovery sequence wherever a sequential relaxation is finite.
--
--   Let $X$ be a pseudometric space, let $P$ be a pre-energy, and let $x\in X$. Assume
--
--   $$
--   P.\operatorname{sequentialRelaxation}.\operatorname{FiniteAt}(x),
--   $$
--
--   meaning that the relaxed energy at $x$ is not $\top$. Then there exists an approximating sequence of concrete tests converging to $x$ whose energies converge in the liminf/limsup sense encoded by `HasRecoverySequenceAt`:
--
--   $$
--   P.\operatorname{HasRecoverySequenceAt}
--   \bigl(P.\operatorname{sequentialRelaxation},x\bigr).
--   $$
--
--   The declaration is `hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt`. It is a general sequential-relaxation result and assumes neither quadraticity nor a Markov property; finiteness at the point is an explicit hypothesis.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/Recovery.lean#L29-L84 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.Recovery`, declaration `FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Analysis.SpecificLimits.Basic
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

theorem FunctionalInequalities.Energy.PreEnergy.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt_408915f {x : X}
    (hfinite : P.sequentialRelaxation.FiniteAt x) :
    P.HasRecoverySequenceAt P.sequentialRelaxation x := by sorry
