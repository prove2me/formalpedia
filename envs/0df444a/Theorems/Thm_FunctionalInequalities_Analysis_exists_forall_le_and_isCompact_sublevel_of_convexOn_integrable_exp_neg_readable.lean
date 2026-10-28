-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_readable
-- name    : FunctionalInequalities.Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:45.927571+00:00
-- url     : https://prove2.me/theorems/d27371ec-adba-4761-8a3a-e229679243d0
-- title:
--   Compact Sublevels From Exponential Integrability
-- statement:
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
--       [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure] {φ : E → ℝ}
--       (hconv : ConvexOn ℝ Set.univ φ) (hint : Integrable (fun x => Real.exp (-φ x)) m) :
--       (∃ y₀ : E, ∀ y, φ y₀ ≤ φ y) ∧ ∀ c : ℝ, IsCompact {y | φ y ≤ c}
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Coercivity`](https://prove2.me/theorems/2ca7e523-4058-4fe5-bce8-76262b1a4a2d).
--
--   [Source excerpt, lines 25–29](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Coercivity.lean#L25-L29) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Lemma A.4 of Letwin (arXiv:2607.24164v1), p. 17, in its coercivity form.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Coercivity.lean#L23-L260 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Coercivity`, declaration `FunctionalInequalities.Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Coercivity

open MeasureTheory

theorem FunctionalInequalities.Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg_readable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure] {φ : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ φ) (hint : Integrable (fun x => Real.exp (-φ x)) m) :
    (∃ y₀ : E, ∀ y, φ y₀ ≤ φ y) ∧ ∀ c : ℝ, IsCompact {y | φ y ≤ c} := by sorry
