-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_eq_of_two_contacts_below_408915f
-- name    : FunctionalInequalities.Analysis.eq_of_two_contacts_below_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:11.992956+00:00
-- url     : https://prove2.me/theorems/35236427-c422-46be-95cd-ac16046d25fe
-- title:
--   Two Below-Level Contacts Coincide
-- statement:
--   This is an auxiliary contact-point uniqueness lemma.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure, and let $u:E\to\mathbb R$ be convex. Fix $x_0,p\in E$ and assume
--   $$u(x_0)+\langle p,x-x_0\rangle\le u(x)\quad\text{for all }x\in E.$$
--   Let $R\in\mathbb R$, assume $\{x:u(x)\le R\}$ is compact, and suppose that every compact $Q\subseteq\{x:u(x)<R\}$ admits two-sided `ENNReal` volume bounds for open $G$ with $\overline G\subseteq Q$:
--   $$\operatorname{ofReal}(a)\,\operatorname{vol}(G)\le\operatorname{vol}(\partial u(G))\le\operatorname{ofReal}(b)\,\operatorname{vol}(G),$$
--   with $a>0$. If $u(x_0)<R$, $u(y)<R$, and
--   $$u(y)=u(x_0)+\langle p,y-x_0\rangle,$$
--   then
--   $$y=x_0.$$
--
--   This technical lemma is used to turn strict exposure into uniqueness of contacts below a level.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1758-L1911 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `_private.FunctionalInequalities.Analysis.Convex.Caffarelli.0.FunctionalInequalities.Analysis.eq_of_two_contacts_below`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F5SublevelContactLemma
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
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
section FiniteDimensional
variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

lemma FunctionalInequalities.Analysis.eq_of_two_contacts_below_408915f {u : E → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ x, u x₀ + ⟪p, x - x₀⟫ ≤ u x) {R : ℝ}
    (hK : IsCompact {x | u x ≤ R})
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {x | u x < R} →
      ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → closure G ⊆ Q →
        ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) (subgradientImage u G) ∧
        (volume : Measure E) (subgradientImage u G) ≤
          ENNReal.ofReal b * (volume : Measure E) G)
    (hxR : u x₀ < R) {y : E} (hyR : u y < R)
    (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀ := by sorry
