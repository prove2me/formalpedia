-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_succ_of_eq_inner_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.taylorTensor_succ_of_eq_inner_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:35.037319+00:00
-- url     : https://prove2.me/theorems/93f25a59-9d8a-4033-a79b-2ccbead0cd07
-- title:
--   Successor Taylor Tensor from an Inner-Product Identity
-- statement:
--   This statement formalizes the tensor identity corresponding to Lemma 3.6 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a real inner-product space that is complete and measurable, let $\mu$ be a measure on $E$, and let $g:E\to\mathbb R$ and $G:E\to E$. Assume:
--
--   1. The tilt average $F_G=\operatorname{tiltAverage}(\mu,G)$ is infinitely continuously differentiable.
--   2. The tilt average of $g$ satisfies, for every $w\in E$,
--      $$
--      F_g(w)=\langle w,F_G(w)\rangle.
--      $$
--   3. $d\in\mathbb N$.
--
--   Then
--
--   $$
--   T_{d+1}g=\operatorname{symmetrizeML}\bigl(\operatorname{appendInner}(T_dG)\bigr).
--   $$
--
--   The result isolates the tensor consequence of the tilt identity and can be reused independently of compact-support assumptions used elsewhere.
--
--   **Formalization Note** The statement has no finite-dimensionality or Borel-space hypothesis. The definitions `tiltAverage`, `taylorTensor`, `appendInner`, and `symmetrizeML` are used exactly as Lean defines them.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem taylorTensor_succ_of_eq_inner (μ : Measure E) {g : E → ℝ} {G : E → E}
--       (hG : ContDiff ℝ ∞ (tiltAverage μ G))
--       (hEq : tiltAverage μ g = fun w => ⟪w, tiltAverage μ G w⟫) (d : ℕ) :
--       taylorTensor μ g (d + 1) = symmetrizeML (appendInner (taylorTensor μ G d))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/SquareIntegrable`](https://prove2.me/theorems/9b0acc03-d3b4-4825-a2f6-2c89b2d937d5).
--
--   Definition modules: [`Analysis/Tensor/Multilinear`](https://prove2.me/theorems/95acd8c3-b570-4032-a49b-c00dac41b021), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`iteratedFDeriv_comp_perm_of_contDiff`](https://prove2.me/theorems/62e73549-6b73-43c8-a852-062236b36219), [`iteratedFDeriv_inner_self_apply`](https://prove2.me/theorems/93b102a6-8056-49d9-b513-0807baf24636), [`sum_perm_inner_init_last`](https://prove2.me/theorems/21685786-ff33-430e-9d2e-110686ae2c53).
--
--   Previous: [`integrable_expTilt_of_memLp`](https://prove2.me/theorems/92338882-be7b-4eaa-bd08-2e7a5b6bd38c).
--
--   [Source excerpt, lines 695–698](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L695-L698) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L691-L733 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.taylorTensor_succ_of_eq_inner`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_succ_of_eq_inner_readable (μ : Measure E) {g : E → ℝ} {G : E → E}
    (hG : ContDiff ℝ ∞ (tiltAverage μ G))
    (hEq : tiltAverage μ g = fun w => ⟪w, tiltAverage μ G w⟫) (d : ℕ) :
    taylorTensor μ g (d + 1) = symmetrizeML (appendInner (taylorTensor μ G d)) := by sorry
