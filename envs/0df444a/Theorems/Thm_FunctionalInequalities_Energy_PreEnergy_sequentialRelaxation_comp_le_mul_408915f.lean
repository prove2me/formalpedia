-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_sequentialRelaxation_comp_le_mul_408915f
-- name    : FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:10.408234+00:00
-- url     : https://prove2.me/theorems/2c35dbd3-a05e-4f28-b868-0d6fe569c953
-- title:
--   Scaled Comparison of Sequential Relaxations
-- statement:
--   This is a general comparison principle for sequential relaxations.
--
--   Let $X$ and $Y$ be topological spaces, let $P$ and $Q$ be pre-energies on $X$ and $Y$, let $T:X\to Y$ be continuous, and let $\kappa\in[0,\infty)$ be an `NNReal`. Assume that every test $f$ of $P$ admits a test $g$ of $Q$ such that
--
--   $$
--   Q.\operatorname{toAmbient}(g)=T(P.\operatorname{toAmbient}(f))
--   $$
--
--   and
--
--   $$
--   Q.\operatorname{energy}(g)\le \kappa\,P.\operatorname{energy}(f).
--   $$
--
--   Then, for every $x\in X$ with finite $P$-sequential relaxation,
--
--   $$
--   Q.\operatorname{sequentialRelaxation}(Tx)
--   \le
--   \kappa\,P.\operatorname{sequentialRelaxation}(x).
--   $$
--
--   This reusable lemma transports finite energy comparisons through continuous maps.
--
--   **Formalization Note** Energies and relaxations take values in $[0,\infty]$ (`ENNReal`), while $\kappa$ is coerced from `NNReal`; the finiteness premise excludes a top-valued source relaxation.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Relaxation/Basic.lean#L109-L136 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Relaxation.Basic`, declaration `FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

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
universe u v
section
namespace FunctionalInequalities.Energy.PreEnergy
end FunctionalInequalities.Energy.PreEnergy
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.PreEnergy
variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)

theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le_mul_408915f {Y : Type*} [TopologicalSpace Y]
    (Q : PreEnergy Y) (T : X → Y) (hT : Continuous T) (κ : NNReal)
    (h : ∀ f : P.Test, ∃ g : Q.Test,
      Q.toAmbient g = T (P.toAmbient f) ∧ (Q.energy g : ENNReal) ≤ κ * P.energy f) (x : X)
    (hx : P.sequentialRelaxation x ≠ ⊤) :
    Q.sequentialRelaxation (T x) ≤ κ * P.sequentialRelaxation x := by sorry
