-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_covariance_pos_readable
-- name    : FunctionalInequalities.KLS.RegularPotential.covariance_pos_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:12.652724+00:00
-- url     : https://prove2.me/theorems/667d09eb-b3ce-45f1-b74f-5f0cda341fe8
-- title:
--   Positive Definiteness of a Regular Law's Covariance
-- statement:
--   This statement asserts strict positivity of the covariance quadratic form of a regular law on every nonzero vector.
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure. Let $V:E\to\mathbb R$ and $a,b\in\mathbb R$, and assume $h_V:$ `KLS.RegularPotential V a b`. Let $\mu$ be the associated probability law `RegularPotential.law hV`, and let $\Sigma_\mu$ denote `Covariance.operator`. For every $v\in E$ with $v\ne0$,
--   $$
--   0<\langle\Sigma_\mu v,v\rangle.
--   $$
--   This positivity statement supplies the nondegeneracy needed for covariance whitening of regular laws.
--
--   **Formalization Note** The regularity and curvature requirements are those of the supplied `RegularPotential` predicate with parameters $a,b$; there is no additional hypothesis $b>0$ in this declaration. Dimension zero is allowed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.RegularPotential`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem covariance_pos (hV : KLS.RegularPotential V a b) {v : E} (hv : v ≠ 0) :
--       0 < inner ℝ (Covariance.operator (hV.law : Measure E) v) v
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Regular/Isotropic`](https://prove2.me/theorems/5550c234-e769-4e96-92d5-32895956f7b0).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342).
--
--   Supporting theorems: [`convexOn_of_hessian_ge`](https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d), [`isBorellDensity_of_eq_tilted`](https://prove2.me/theorems/0d7194a7-857d-46cc-b91c-8366be9b61de), [`memLp_id_two`](https://prove2.me/theorems/1e1255d8-1cf4-45ef-8f96-0337bafe649e).
--
--   Next: [`isotropic_comp_affine_of_whitening`](https://prove2.me/theorems/250f40f4-c071-4d51-ae87-70dd46460141).
--
--   [Source excerpt, lines 46–47](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Isotropic.lean#L46-L47) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Isotropic.lean#L45-L64 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Regular.Isotropic`, declaration `FunctionalInequalities.KLS.RegularPotential.covariance_pos`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Isotropic

open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {V : E → ℝ} {a b : ℝ}

theorem FunctionalInequalities.KLS.RegularPotential.covariance_pos_readable (hV : KLS.RegularPotential V a b) {v : E} (hv : v ≠ 0) :
    0 < inner ℝ (Covariance.operator (hV.law : Measure E) v) v := by sorry
