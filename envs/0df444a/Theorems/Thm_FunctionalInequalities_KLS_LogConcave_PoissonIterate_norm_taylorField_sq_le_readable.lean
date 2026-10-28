-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_norm_taylorField_sq_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_taylorField_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:45.870397+00:00
-- url     : https://prove2.me/theorems/658d541a-caf2-439c-ac49-7e33a7865643
-- title:
--   Componentwise Taylor-Field Bound
-- statement:
--   This statement is the componentwise extension of the Taylor bound to tensor fields.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $\nu$ be a probability measure on $V$, and let $R\in\mathbb R$ and $d\in\mathbb N$. Assume that for every scalar $g\in L^2(\nu)$,
--   $$\|T_d g\|\le R^d\|g\|,$$
--   where the tensor norm is the Hilbert–Schmidt norm in the standard orthonormal basis. For any rank-$k$ tensor field $u$ represented by `Field ν k`, the corresponding `taylorField` satisfies
--   $$\|T_d u\|^2\le R^{2d}\,\operatorname{normSq}(u).$$
--
--   The result packages a scalar Taylor estimate into the squared norm estimate needed for sums over tensor components. It is reusable whenever a tensor field is handled componentwise.
--
--   **Formalization Note.** `normSq` is the squared Euclidean norm of the field, and all norms in the conclusion are ordinary real norms.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_taylorField_sq_le {R : ℝ} {d : ℕ}
--       (h29 : ∀ g : Lp ℝ 2 (ν : Measure V),
--         ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑g) d)‖ ≤
--           R ^ d * ‖g‖) {k : ℕ} (u : Field ν k) :
--       ‖taylorField d u‖ ^ 2 ≤ R ^ (2 * d) * normSq u
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Criterion`](https://prove2.me/theorems/b6210dc1-894e-490a-a262-24735151f6b5).
--
--   Definition modules: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Previous: [`le_of_iterate_bounds`](https://prove2.me/theorems/f80538b2-5d61-41ae-9ced-cdc9bb4e7bf2) · Next: [`taylorCriterion`](https://prove2.me/theorems/02b2baa1-1cb3-4817-9e35-5dc605a75700).
--
--   [Source excerpt, lines 346–350](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean#L346-L350) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean#L343-L361 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_taylorField_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion

open MeasureTheory Filter Topology Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] {ν : MeasureTheory.ProbabilityMeasure V}

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_taylorField_sq_le_readable {R : ℝ} {d : ℕ}
    (h29 : ∀ g : Lp ℝ 2 (ν : Measure V),
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑g) d)‖ ≤
        R ^ d * ‖g‖) {k : ℕ} (u : Field ν k) :
    ‖taylorField d u‖ ^ 2 ≤ R ^ (2 * d) * normSq u := by sorry
