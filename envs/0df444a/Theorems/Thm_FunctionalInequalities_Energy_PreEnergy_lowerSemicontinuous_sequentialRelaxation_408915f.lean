-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_lowerSemicontinuous_sequentialRelaxation_408915f
-- name    : FunctionalInequalities.Energy.PreEnergy.lowerSemicontinuous_sequentialRelaxation_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:49.025025+00:00
-- url     : https://prove2.me/theorems/b3837e2b-7982-4ea5-b8b3-310f273a2f2f
-- title:
--   Lower Semicontinuity Of Sequential Relaxation
-- statement:
--   This theorem states that sequential relaxation is lower semicontinuous in a pseudometric ambient space.
--
--   Let $X$ be a pseudometric space and let $P$ be any pre-energy on $X$. Then the function assigning to $x\in X$ the `ENNReal`-valued sequentially relaxed energy is lower semicontinuous:
--
--   $$
--   \operatorname{LowerSemicontinuous}\!\left(
--    x\mapsto P.\operatorname{sequentialRelaxation}(x)
--   \right).
--   $$
--
--   The declaration is `lowerSemicontinuous_sequentialRelaxation`. The conclusion allows relaxed energy equal to $\top$ and does not require a dense realization, quadratic structure, closability, or a Markov property.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/LowerSemicontinuous.lean#L31-L78 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous`, declaration `FunctionalInequalities.Energy.PreEnergy.lowerSemicontinuous_sequentialRelaxation`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
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
section Semicontinuity
universe u
variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)

theorem FunctionalInequalities.Energy.PreEnergy.lowerSemicontinuous_sequentialRelaxation_408915f :
    LowerSemicontinuous (fun x ↦ P.sequentialRelaxation x) := by sorry
