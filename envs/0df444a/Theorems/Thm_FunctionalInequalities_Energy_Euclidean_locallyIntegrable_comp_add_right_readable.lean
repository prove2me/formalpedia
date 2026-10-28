-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_locallyIntegrable_comp_add_right_readable
-- name    : FunctionalInequalities.Energy.Euclidean.locallyIntegrable_comp_add_right_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:16.312661+00:00
-- url     : https://prove2.me/theorems/20004fc3-1194-490c-af8c-f5c2147ffe0b
-- title:
--   Local Integrability Under Haar Translation
-- statement:
--   This states stability of local integrability under translation.
--
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $m$ be an additive Haar measure on $V$, and let $h:V\to\mathbb R$ be locally integrable with respect to $m$. For every $v\in V$, the translated function
--
--   $$
--    x\longmapsto h(x+v)
--   $$
--
--   is also locally integrable with respect to $m$.
--
--   This is a measure-theoretic auxiliary fact used when comparing a function with its translates in weak-gradient arguments.
--
--   **Formalization Note** The declaration omits the second-countable-topology assumption; the additive Haar-measure instance is explicit.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.Euclidean`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem locallyIntegrable_comp_add_right {h : V → ℝ} (hh : LocallyIntegrable h m) (v : V) :
--       LocallyIntegrable (fun x => h (x + v)) m
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/ZeroGradient`](https://prove2.me/theorems/52f28c92-8879-4a35-be78-f95c88a2a467).
--
--   Previous: [`integral_mul_sub_translate_eq_zero`](https://prove2.me/theorems/92d2bdd3-6571-4798-95e4-ba80de2514d6) · Next: [`ae_add_eq_of_integral_mul_fderiv_eq_zero`](https://prove2.me/theorems/41fc0968-9c28-44e9-bc3c-b52d1929e169).
--
--   [Source excerpt, lines 252–253](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L252-L253) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L250-L266 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.locallyIntegrable_comp_add_right`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient

open MeasureTheory Filter Topology
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
omit [SecondCountableTopology V]

theorem FunctionalInequalities.Energy.Euclidean.locallyIntegrable_comp_add_right_readable {h : V → ℝ} (hh : LocallyIntegrable h m) (v : V) :
    LocallyIntegrable (fun x => h (x + v)) m := by sorry
