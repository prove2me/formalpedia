-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_poincare_le_of_cumulantBound_readable
-- name    : FunctionalInequalities.KLS.RegularPotential.poincare_le_of_cumulantBound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:14.569001+00:00
-- url     : https://prove2.me/theorems/0b4bd144-4221-4e5f-a91d-90cbadac41af
-- title:
--   Poincaré Bound for Isotropic Regular Laws
-- statement:
--   This formalizes the regular-law part of the Bizeul–Klartag–Lehec reduction described on p. 30; it is conditional on the cumulant bounds used there.
--
--   There exists a real constant $C>0$ such that, for every $K\in\mathbb R$ with $1\le K$, the following implication holds: if, for every $d\in\mathbb N$ with $2\le d$, `CumulantBound d ((d!)² K^d)` holds, then for every $n\in\mathbb N$, every $V:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin} n)\to\mathbb R$, every $a,b\in\mathbb R$, and every regular potential $hV : KLS.RegularPotential V a b$ whose law is isotropic,
--
--   $$
--   \operatorname{constant}_{\mathrm{Intrinsic}}(\operatorname{law}(hV))
--   \le \operatorname{ENNReal.ofReal}(2CK).
--   $$
--
--   Here `Poincare.LocalSlope.Intrinsic.constant` is the Poincaré constant used by the formalization, with values in $[0,\infty]$.
--
--   This declaration supplies the regular finite-dimensional estimate that is later extended from regular laws to arbitrary finite-dimensional isotropic log-concave probability measures.
--
--   **Formalization Note**: The conclusion is an inequality in `ENNReal`; the right-hand side is `ENNReal.ofReal (2 * C * K)`. No universal cumulant bound is discharged by this declaration.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.RegularPotential`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem poincare_le_of_cumulantBound :
--       ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
--         (∀ d : ℕ, 2 ≤ d → CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) →
--         ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ) (hV : KLS.RegularPotential V a b),
--           KLS.Isotropic hV.law →
--           Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (2 * C * K)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Reduction`](https://prove2.me/theorems/777aa78c-b385-4e2a-916c-1b5126410eae).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Selected supporting theorems: [`convexOn_of_hessian_ge`](https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d), [`sum_coordTensor_sq_eq`](https://prove2.me/theorems/43928816-0a65-4412-bbe2-8abe0018771e), [`Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries`](https://prove2.me/theorems/368cfad9-ddaa-46ae-9c1e-acc8bb0d753f), [`taylorCriterion`](https://prove2.me/theorems/02b2baa1-1cb3-4817-9e35-5dc605a75700), [`norm_coordTensor_taylorTensor_sq_le_two_mul`](https://prove2.me/theorems/b022259f-6e00-41ce-bbc5-b1bff64f4b1e).
--
--   Previous: [`Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries`](https://prove2.me/theorems/368cfad9-ddaa-46ae-9c1e-acc8bb0d753f) · Next: [`localSlope_le_of_cumulantBound_all`](https://prove2.me/theorems/cb774c5b-d478-4527-a81e-37c436cdedf4).
--
--   [Source excerpt, lines 181–186](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Reduction.lean#L181-L186) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 1.1, p. 2. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Reduction.lean#L174-L294 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Reduction`, declaration `FunctionalInequalities.KLS.RegularPotential.poincare_le_of_cumulantBound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Reduction

open FunctionalInequalities.KLS.LogConcave.Suspension

theorem FunctionalInequalities.KLS.RegularPotential.poincare_le_of_cumulantBound_readable :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
      (∀ d : ℕ, 2 ≤ d → CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) →
      ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ) (hV : KLS.RegularPotential V a b),
        KLS.Isotropic hV.law →
        Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (2 * C * K) := by sorry
