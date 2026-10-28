-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_isotropic_comp_affine_of_whitening_readable
-- name    : FunctionalInequalities.KLS.RegularPotential.isotropic_comp_affine_of_whitening_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:53.833992+00:00
-- url     : https://prove2.me/theorems/250f40f4-c071-4d51-ae87-70dd46460141
-- title:
--   Isotropy of a Centered and Whitened Regular Potential
-- statement:
--   This statement identifies the isotropy of the law of a specified affine transformation of a regular potential.
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure. Let $V:E\to\mathbb R$, $a,b\in\mathbb R$, and $h_V:$ `KLS.RegularPotential V a b`. Write $\mu=$ `RegularPotential.law hV`, $c=\int x\,d\mu(x)$, and $\Sigma_\mu=$ `Covariance.operator μ`. Assume:
--
--   1. $W:E\to E$ is an invertible continuous linear map and $W^*=W$.
--   2. For every $u,v\in E$, $\langle\Sigma_\mu(Wu),Wv\rangle=\langle u,v\rangle$.
--
--   Let $\widetilde\mu$ be the law supplied by `RegularPotential.comp_affine hV W.symm c`, corresponding to the potential $y\mapsto V(W^{-1}y+c)$. Then
--   $$
--   \operatorname{Isotropic}(\widetilde\mu).
--   $$
--   Here `KLS.Isotropic` means finite second moment, zero mean, and identity centered covariance. This is a normalization result for a supplied whitening map, not an assertion of its existence or uniqueness.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.RegularPotential`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem isotropic_comp_affine_of_whitening (hV : KLS.RegularPotential V a b)
--       (W : E ≃L[ℝ] E) (hWadj : (W : E →L[ℝ] E).adjoint = W)
--       (hW : ∀ u v, inner ℝ (Covariance.operator (hV.law : Measure E) (W u)) (W v) = inner ℝ u v) :
--       KLS.Isotropic (comp_affine hV W.symm
--         (∫ x, x ∂(hV.law : Measure E))).law
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Regular/Isotropic`](https://prove2.me/theorems/5550c234-e769-4e96-92d5-32895956f7b0).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342).
--
--   Supporting theorems: [`convexOn_of_hessian_ge`](https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d), [`Covariance.operator_map_continuousLinearEquiv`](https://prove2.me/theorems/4b0ba356-0a64-4912-a8f7-67b0e65a1329), [`isBorellDensity_of_eq_tilted`](https://prove2.me/theorems/0d7194a7-857d-46cc-b91c-8366be9b61de), [`memLp_id_two`](https://prove2.me/theorems/1e1255d8-1cf4-45ef-8f96-0337bafe649e), [`RegularPotential.law_comp_affine`](https://prove2.me/theorems/a3faf409-b5c0-4734-ac62-cbff615f4315).
--
--   Previous: [`covariance_pos`](https://prove2.me/theorems/667d09eb-b3ce-45f1-b74f-5f0cda341fe8).
--
--   [Source excerpt, lines 75–79](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Isotropic.lean#L75-L79) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Isotropic.lean#L73-L96 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Regular.Isotropic`, declaration `FunctionalInequalities.KLS.RegularPotential.isotropic_comp_affine_of_whitening`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Isotropic

open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {V : E → ℝ} {a b : ℝ}

theorem FunctionalInequalities.KLS.RegularPotential.isotropic_comp_affine_of_whitening_readable (hV : KLS.RegularPotential V a b)
    (W : E ≃L[ℝ] E) (hWadj : (W : E →L[ℝ] E).adjoint = W)
    (hW : ∀ u v, inner ℝ (Covariance.operator (hV.law : Measure E) (W u)) (W v) = inner ℝ u v) :
    KLS.Isotropic (comp_affine hV W.symm
      (∫ x, x ∂(hV.law : Measure E))).law := by sorry
