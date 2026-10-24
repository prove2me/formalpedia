-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_exists_adjointComp_eq_of_gap_408915f
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.exists_adjointComp_eq_of_gap_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:06.160806+00:00
-- url     : https://prove2.me/theorems/a26ea46b-45ad-408c-a48b-5cae14100c7d
-- title:
--   Solvability of the Adjoint-Composition Equation
-- statement:
--   This is an existence theorem for the equation $Au=g$ on the orthogonal complement of $\ker T$.
--
--   Let $H_0,H_1$ be complete real Hilbert spaces, let $T:H_0\to H_1$ be closed with dense domain, and write $A=T^\dagger T$. Fix $C\in\mathbb{R}$ and assume the gap condition
--
--   $$\|y\|^2\le C\|Ty\|^2$$
--
--   for every $y\in D(T)$ orthogonal to $\ker T$. If $g\in H_0$ is orthogonal to every $k\in D(T)$ with $Tk=0$, then there exists $u\in D(A)$ such that
--
--   $$u\perp\ker T\qquad\text{and}\qquad Au=g.$$
--
--   This provides existence of an inverse on the kernel complement; uniqueness is supplied by the corresponding uniqueness lemma.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Inverse.lean#L150-L234 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Inverse`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.exists_adjointComp_eq_of_gap`; the repository is private at upload time).

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
open scoped InnerProductSpace RealInnerProductSpace
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
open Filter Topology Set
include hT hd

theorem FunctionalInequalities.Analysis.Semigroup.Generated.exists_adjointComp_eq_of_gap_408915f {C : ℝ}
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      ‖(y : H₀)‖ ^ 2 ≤ C * ‖T y‖ ^ 2)
    (g : H₀) (hg : ∀ k : T.domain, T k = 0 → ⟪g, (k : H₀)⟫ = 0) :
    ∃ u : (adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) ∧ adjointComp T u = g := by sorry
