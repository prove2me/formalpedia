-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_eq_of_adjointComp_eq_408915f
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.eq_of_adjointComp_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:08:39.158386+00:00
-- url     : https://prove2.me/theorems/b57a674c-5c25-4a24-a373-3607867baa9a
-- title:
--   Uniqueness on the Orthogonal Complement of the Kernel
-- statement:
--   This is a uniqueness lemma for the operator $A=T^\dagger T$.
--
--   Let $H_0,H_1$ be real Hilbert spaces, with $H_0$ complete, and let $T:H_0\to H_1$ be a linear partial map whose domain is dense in $H_0$. Let $u,v$ belong to the domain of `adjointComp T`, and assume:
--
--   1. $u$ is orthogonal to every $k\in D(T)$ satisfying $Tk=0$.
--   2. $v$ is orthogonal to every such $k$.
--   3. $Au=Av$, where $A=\operatorname{adjointComp}(T)$.
--
--   Then
--
--   $$u=v.$$
--
--   The conclusion identifies two operator-domain vectors with the same image under $T^\dagger T$ once both are orthogonal to $\ker T$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Inverse.lean#L236-L259 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Inverse`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.eq_of_adjointComp_eq`; the repository is private at upload time).

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
omit [CompleteSpace H₁]
include hd

theorem FunctionalInequalities.Analysis.Semigroup.Generated.eq_of_adjointComp_eq_408915f (u v : (adjointComp T).domain)
    (hu : ∀ k : T.domain, T k = 0 → ⟪(u : H₀), (k : H₀)⟫ = 0)
    (hv : ∀ k : T.domain, T k = 0 → ⟪(v : H₀), (k : H₀)⟫ = 0)
    (huv : adjointComp T u = adjointComp T v) : (u : H₀) = v := by sorry
