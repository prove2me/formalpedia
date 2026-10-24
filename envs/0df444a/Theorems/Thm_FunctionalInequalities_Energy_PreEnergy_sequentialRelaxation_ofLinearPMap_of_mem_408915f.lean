-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_sequentialRelaxation_ofLinearPMap_of_mem_408915f
-- name    : FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:50.924518+00:00
-- url     : https://prove2.me/theorems/cd5696ed-a31c-4f19-8405-1b155d421c10
-- title:
--   Exact Relaxed Energy On The Closure Domain
-- statement:
--   This theorem identifies the sequential relaxation of a closable partial linear operator on the domain of its closure.
--
--   Let $X$ be a real normed space, let $H$ be a complete real Hilbert space, and let $T:X\dashrightarrow H$ be closable. For every $x\in\operatorname{dom}(\overline T)$,
--
--   $$
--   \operatorname{sequentialRelaxation}_{T}(x)
--   =
--   \|\overline T x\|_{+}^{\,2}.
--   $$
--
--   The left side is the `ENNReal`-valued sequential relaxation of the pre-energy `PreEnergy.ofLinearPMap T`; the right side is the square of the `NNReal` norm, coerced to `ENNReal`. The declaration is `sequentialRelaxation_ofLinearPMap_of_mem`, and the equality is asserted only for points in the closure domain.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean#L357-L382 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.LinearPMap`, declaration `FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open Filter Topology Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section PreEnergy
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
variable (T : X →ₗ.[ℝ] H)

theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem_408915f (hT : T.IsClosable) (x : T.closure.domain) :
    (ofLinearPMap T).sequentialRelaxation x = (‖T.closure x‖₊ ^ 2 : NNReal) := by sorry
