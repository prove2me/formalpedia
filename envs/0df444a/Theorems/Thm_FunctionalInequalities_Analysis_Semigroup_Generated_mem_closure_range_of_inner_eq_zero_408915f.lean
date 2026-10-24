-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_mem_closure_range_of_inner_eq_zero_408915f
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.mem_closure_range_of_inner_eq_zero_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:54.677563+00:00
-- url     : https://prove2.me/theorems/8ebe8398-30a5-43b4-9ea3-37cbbf8d0213
-- title:
--   Orthogonality to the Kernel Implies Closure of the Range
-- statement:
--   This is a range-closure characterization for $A=T^\dagger T$.
--
--   Let $H_0,H_1$ be complete real Hilbert spaces, let $T:H_0\to H_1$ be closed, and assume $D(T)$ is dense in $H_0$. If $g\in H_0$ satisfies
--
--   $$\langle g,k\rangle=0$$
--
--   for every $k\in D(A)$ with $Ak=0$, where $A=\operatorname{adjointComp}(T)$, then
--
--   $$g\in\overline{\operatorname{range}(A)}.$$
--
--   The closure is taken in $H_0$. This is a standard Hilbert-space ingredient for approximation by the range of a self-adjoint operator.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean#L100-L141 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Convergence`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.mem_closure_range_of_inner_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Dissipation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_FormDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Smoothing
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.LinearPMap

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace LinearPMap
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Semigroup
end FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup
section
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
include hT hd

theorem FunctionalInequalities.Analysis.Semigroup.Generated.mem_closure_range_of_inner_eq_zero_408915f (g : H₀)
    (hg : ∀ k : (adjointComp T).domain, adjointComp T k = 0 → ⟪g, (k : H₀)⟫ = 0) :
    g ∈ closure (Set.range fun y : (adjointComp T).domain => adjointComp T y) := by sorry
