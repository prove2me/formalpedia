-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_taylorTensor_center_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_center_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:36.56498+00:00
-- url     : https://prove2.me/theorems/2224e876-b11e-4fc6-980d-876a9062141d
-- title:
--   Taylor Tensors Ignore Centering
-- statement:
--   Let $\nu$ be a probability measure on a finite-dimensional Borel space with all exponential moments, let $u\in L^2(\nu)$, and let $d\ge1$. Then the degree-$d$ Taylor tensor is unchanged by centering:
--
--   $$T_d\left(u-\int u\,d\nu\right)=T_d(u).$$
--
--   Equivalently, using the formalization's `L2.center`,
--
--   $$T_d(\operatorname{center}(u))=T_d(u).$$
--
--   This is a technical fact used to replace weak derivatives by their centered versions in Taylor-tensor identities. No finite-dimensional assumption is required by this declaration beyond the Borel structure shown in the type.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem taylorTensor_center
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
--       (u : Lp ℝ 2 (ν : Measure V)) {d : ℕ} (hd : 1 ≤ d) :
--       taylorTensor (ν : Measure V) (⇑(L2.center ν u)) d = taylorTensor (ν : Measure V) (⇑u) d
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Taylor`](https://prove2.me/theorems/4a314a0c-259a-4368-99cf-b24123869fe0).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Supporting theorems: [`integrable_expTilt_of_memLp`](https://prove2.me/theorems/92338882-be7b-4eaa-bd08-2e7a5b6bd38c).
--
--   Next: [`symmetrize_apply_comp_cast`](https://prove2.me/theorems/f3dc6e21-450b-4d16-aab4-8e4451661aaa).
--
--   [Source excerpt, lines 96–99](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L96-L99) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L94-L110 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_center`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor

open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [FiniteDimensional ℝ V]

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_center_readable
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (u : Lp ℝ 2 (ν : Measure V)) {d : ℕ} (hd : 1 ≤ d) :
    taylorTensor (ν : Measure V) (⇑(L2.center ν u)) d = taylorTensor (ν : Measure V) (⇑u) d := by sorry
