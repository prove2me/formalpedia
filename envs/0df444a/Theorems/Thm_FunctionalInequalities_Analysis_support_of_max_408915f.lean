-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_support_of_max_408915f
-- name    : FunctionalInequalities.Analysis.support_of_max_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:34.315291+00:00
-- url     : https://prove2.me/theorems/3a19c585-b9c2-48a0-9663-cef46255296e
-- title:
--   Supporting Hyperplane From an Interior Maximum
-- statement:
--   This is a technical supporting-hyperplane lemma for a convex function.
--
--   Let $E$ be a real inner-product normed additive group, let $u:E\to\mathbb R$ be convex on all of $E$, and let $\Omega\subseteq E$ be open. For $x_0,x_1,p\in E$ and $c\in\mathbb R$, assume $x_1\in\Omega$ and that $x_1$ maximizes
--   $$z\mapsto c+\langle p,z-x_0\rangle-u(z)$$
--   on over $\overline\Omega$. Then, for every $y\in E$,
--   $$u(x_1)+\langle p,y-x_1\rangle\le u(y).$$
--
--   The result identifies $p$ as a subgradient of $u$ at $x_1$, using the inline subgradient formulation rather than a separate subdifferential object. It is used to convert a maximizer of an affine perturbation into a global supporting inequality.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L870-L981 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `_private.FunctionalInequalities.Analysis.Convex.Subgradient.0.FunctionalInequalities.Analysis.support_of_max`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT12ASubgradientImageMonotone
open Set
open scoped RealInnerProductSpace
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma FunctionalInequalities.Analysis.support_of_max_408915f
    {u : E → ℝ} {Ω : Set E} (hu : ConvexOn ℝ univ u) (hΩ : IsOpen Ω)
    (x₀ x₁ p : E) (c : ℝ) (hx₁ : x₁ ∈ Ω)
    (hmax :
      IsMaxOn (fun z => c + ⟪p, z - x₀⟫ - u z) (closure Ω) x₁) :
    ∀ y, u x₁ + ⟪p, y - x₁⟫ ≤ u y := by sorry
