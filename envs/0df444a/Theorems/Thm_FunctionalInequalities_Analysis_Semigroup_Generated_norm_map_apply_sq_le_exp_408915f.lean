-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_map_apply_sq_le_exp_408915f
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:09.669301+00:00
-- url     : https://prove2.me/theorems/4b75a002-5299-4dc5-b238-7c6c9da62be5
-- title:
--   Exponential Energy Decay on the Form Domain
-- statement:
--   This is the exponential energy estimate on the full form domain under the curvature bound.
--
--   Let $H_0,H_1$ be real complete inner-product spaces, let $T:H_0\to H_1$ be closed with dense domain, and set $A=T^\dagger T$. Let $\rho\in\mathbb R$ and assume
--
--   $$
--   \rho\,\|Ty\|^2\le\|Ay\|^2\qquad\text{for every }y\in D(A).
--   $$
--
--   Then for every $f\in D(T)$ and every $t\ge0$,
--
--   $$
--   \|T(P_t f)\|^2\le e^{-2\rho t}\,\|Tf\|^2.
--   $$
--
--   This extends the decay estimate from $D(A)$ to $D(T)$ and is the principal semigroup energy estimate in this development.
--
--   **Formalization Note.** The conclusion concerns the form domain $D(T)$, while the curvature hypothesis ranges over $D(A)$; $P_t$ is `Generated.apply T hT hd t`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Curvature.lean#L306-L427 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Curvature`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp`; the repository is private at upload time).

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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.LinearPMap

noncomputable section
open Filter Topology Set
open scoped RealInnerProductSpace
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

theorem FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_exp_408915f {ρ : ℝ}
    (hcurv : ∀ y : (adjointComp T).domain, ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2)
    (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
    ‖T ⟨apply T hT hd t f, preserves_form_domain T hT hd f ht⟩‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) * ‖T f‖ ^ 2 := by sorry
