-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_readable
-- name    : FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:16.934398+00:00
-- url     : https://prove2.me/theorems/582959f3-9760-49aa-8308-fec3d495a4ec
-- title:
--   Almost-Everywhere Constancy From Translation Invariance
-- statement:
--   This is a measurable translation-invariance criterion for almost-everywhere constancy.
--
--   Let $V$ be a finite-dimensional real inner-product normed additive group with its Borel measurable structure, and let $m$ be an additive Haar measure. For a measurable function $g:V\to\mathbb R$, assume that every translation preserves $g$ almost everywhere:
--
--   $$
--   \forall v\in V,\qquad g(x+v)=g(x)\quad\text{for $m$-almost every }x.
--   $$
--
--   Then there exists a constant $c\in\mathbb R$ such that
--
--   $$
--    g(x)=c\quad\text{for $m$-almost every }x.
--   $$
--
--   The Lean declaration is `exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_readable`. It is a reusable measure-theoretic auxiliary lemma; the conclusion is existential and only asserts equality almost everywhere.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.Euclidean`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_ae_eq_const_of_measurable_of_forall_ae_add_eq {g : V → ℝ} (hg : Measurable g)
--       (htr : ∀ v : V, ∀ᵐ x ∂m, g (x + v) = g x) :
--       ∃ c : ℝ, ∀ᵐ x ∂m, g x = c
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/ZeroGradient`](https://prove2.me/theorems/52f28c92-8879-4a35-be78-f95c88a2a467).
--
--   Previous: [`ae_add_eq_of_integral_mul_fderiv_eq_zero`](https://prove2.me/theorems/41fc0968-9c28-44e9-bc3c-b52d1929e169).
--
--   [Source excerpt, lines 342–344](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L342-L344) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L340-L370 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_measurable_of_forall_ae_add_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient

universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_readable {g : V → ℝ} (hg : Measurable g)
    (htr : ∀ v : V, ∀ᵐ x ∂m, g (x + v) = g x) :
    ∃ c : ℝ, ∀ᵐ x ∂m, g x = c := by sorry
