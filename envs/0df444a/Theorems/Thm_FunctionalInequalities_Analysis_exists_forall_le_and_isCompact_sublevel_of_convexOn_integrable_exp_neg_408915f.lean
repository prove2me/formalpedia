-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_408915f
-- name    : FunctionalInequalities.Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:14:45.745921+00:00
-- url     : https://prove2.me/theorems/7e314d36-3388-413c-a841-810188e680a7
-- title:
--   Compact Sublevels From Exponential Integrability
-- statement:
--   This formalizes Lemma A.4 of Letwin (arXiv:2607.24164v1), p. 17, in its coercivity form.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $m$ be an additive Haar measure on $E$, and let $\varphi:E\to\mathbb R$ be convex. Assume
--   $$e^{-\varphi}\text{ is integrable with respect to }m.$$
--   Then $\varphi$ has a global minimizer and every real sublevel set is compact:
--   $$\exists y_0\in E,\ \forall y\in E,\ \varphi(y_0)\le\varphi(y),$$
--   and
--   $$\forall c\in\mathbb R,\quad\{y:\varphi(y)\le c\}\text{ is compact}.$$
--
--   This gives the compactness and attainment properties required for finite-dimensional convex potentials with integrable exponential weight.
--
--   **Formalization Note** No normalization of the integral is assumed; only `Integrable` is required. Dimension zero is included.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Coercivity.lean#L23-L260 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Coercivity`, declaration `FunctionalInequalities.Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`; the repository is private at upload time).

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Order.Compact

open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_408915f
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure] {φ : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ φ) (hint : Integrable (fun x => Real.exp (-φ x)) m) :
    (∃ y₀ : E, ∀ y, φ y₀ ≤ φ y) ∧ ∀ c : ℝ, IsCompact {y | φ y ≤ c} := by sorry
