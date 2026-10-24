-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_exists_approx_eigenvector_of_gap_408915f
-- name    : FunctionalInequalities.Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:14.273039+00:00
-- url     : https://prove2.me/theorems/4a71e787-98db-4d20-9dd1-01562387754f
-- title:
--   Approximate Eigenvectors at the Bottom of the Operator Spectrum
-- statement:
--   This is an approximate-eigenvector construction for $A=T^\dagger T$.
--
--   Let $H_0,H_1$ be complete real Hilbert spaces, let $T:H_0\to H_1$ be closed with dense domain, and let $\lambda,\eta\in\mathbb{R}$ with $\lambda>0$. Assume:
--
--   1. For every $y\in D(T)$ orthogonal to $\ker T$, $\lambda\|y\|^2\le\|Ty\|^2$.
--   2. $y\in D(T)$ is orthogonal to $\ker T$.
--   3. $\|y\|=1$.
--   4. $\|Ty\|^2\le\lambda(1+\eta)$.
--
--   Then there exists $z\in D(A)$, orthogonal to $\ker T$, such that
--
--   $$\|y-z\|\le\sqrt{\eta/8},$$
--   $$\|Az-\lambda z\|\le\lambda\sqrt{\eta/2}.$$
--
--   The theorem does not assume $\eta\ge0$ in its type and does not assert the existence of an exact eigenvector.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/ApproximateEigenvector.lean#L49-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.ApproximateEigenvector`, declaration `FunctionalInequalities.Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap_408915f (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {lam η : ℝ} (hlam : 0 < lam)
    (hgap : ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      lam * ‖(y : H₀)‖ ^ 2 ≤ ‖T y‖ ^ 2)
    (y : T.domain) (hy : ∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0)
    (hy1 : ‖(y : H₀)‖ = 1) (hTy : ‖T y‖ ^ 2 ≤ lam * (1 + η)) :
    ∃ z : (adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(z : H₀), (k : H₀)⟫ = 0) ∧
      ‖(y : H₀) - (z : H₀)‖ ≤ Real.sqrt (η / 8) ∧
      ‖adjointComp T z - lam • (z : H₀)‖ ≤ lam * Real.sqrt (η / 2) := by sorry
