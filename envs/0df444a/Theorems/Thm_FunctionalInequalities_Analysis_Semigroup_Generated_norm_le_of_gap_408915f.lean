-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_le_of_gap_408915f
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:14.396431+00:00
-- url     : https://prove2.me/theorems/74b6c14a-099c-4a88-80be-086f5aff3a66
-- title:
--   Operator-Domain Bounds from a Kernel-Complement Gap
-- statement:
--   This is the norm and energy estimate obtained from a gap inequality.
--
--   Let $H_0,H_1$ be real Hilbert spaces, let $T:H_0\to H_1$ be a linear partial map with dense domain, and let $A=T^\dagger T$. Fix $C\in\mathbb{R}$. Assume that every $y\in D(T)$ orthogonal to $\ker T$ satisfies
--
--   $$\|y\|^2\le C\|Ty\|^2.$$
--
--   For every $u\in D(A)$ orthogonal to $\ker T$, the conclusion is
--
--   $$\|u\|\le C\|Au\|,$$
--   $$\|Tu\|^2=\langle Au,u\rangle,$$
--   $$\langle Au,u\rangle\le C\|Au\|^2.$$
--
--   The statement includes the case of arbitrary real $C$; no positivity assumption on $C$ appears in the type.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Inverse.lean#L23-L104 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Inverse`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap`; the repository is private at upload time).

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
omit [CompleteSpace H₁]
include hd

theorem FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap_408915f {C : ℝ}
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      ‖(y : H₀)‖ ^ 2 ≤ C * ‖T y‖ ^ 2)
    (u : (adjointComp T).domain)
    (hu : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0) :
    ‖(u : H₀)‖ ≤ C * ‖adjointComp T u‖ ∧
      ‖T ⟨(u : H₀), u.2.2⟩‖ ^ 2 = ⟪adjointComp T u, (u : H₀)⟫ ∧
      ⟪adjointComp T u, (u : H₀)⟫ ≤ C * ‖adjointComp T u‖ ^ 2 := by sorry
