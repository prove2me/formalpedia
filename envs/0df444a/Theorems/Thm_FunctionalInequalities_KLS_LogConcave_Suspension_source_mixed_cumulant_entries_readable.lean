-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_source_mixed_cumulant_entries_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.source_mixed_cumulant_entries_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:32.314655+00:00
-- url     : https://prove2.me/theorems/64ef58a4-ed4b-40d5-9f37-7e5aad5551d2
-- title:
--   Mixed Cumulant Entries of the Regular Suspension Joint Law
-- statement:
--   This auxiliary lemma states the mixed-cumulant entry identity corresponding to BKL equation (112).
--
--   Let $n,N\in\mathbb N$ with $N>0$ and $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`). Let $h_V:$ `RegularPotential` $V\ a\ b'$: $a,b'>0$, $V$ is smooth with derivatives of polynomial growth, and $a\operatorname{Id}\le D^2V\le b'\operatorname{Id}$. Put $\mu=h_V.\text{law}$, the normalized $e^{-V}$ law. Assume:
--   1. $\beta>0$, $f:E\to\mathbb R$ is $C^2$, and $\|D(Df)(x)\|\le M$ for every $x$.
--   2. $(\beta/\sqrt N)M\le a$.
--
--   Set $\sigma_\beta=\sqrt{1+2/\beta^2}$ (`sigma`) and $\lambda=$ `jointLaw` $\mu\ f\ \beta\ \sigma_\beta\ N$ on $H=$ `JointSpace` $N\ n$. Let $e_0,e_{(i,j)}$ be its scalar and copy-coordinate unit vectors, and $(b_j)$ the standard basis of $E$. For every natural $d\ge1$, $I:\operatorname{Fin}d\to\operatorname{Fin}N$, and $J:\operatorname{Fin}d\to\operatorname{Fin}n$,
--   $$
--   \kappa_{d+1}^{\lambda}(e_0,e_{(I_k,J_k)}:k\in\operatorname{Fin}d)=
--   \begin{cases}
--   \dfrac{d!}{\sigma_\beta\sqrt N}\,T_d^\mu f(b_{J_k}:k\in\operatorname{Fin}d),&\forall k,k',\ I_k=I_{k'},\\
--   0,&\text{otherwise}.
--   \end{cases}
--   $$
--
--   Here $\kappa_{d+1}^{\lambda}$ is `cumulant` and $T_d^\mu f$ is `taylorTensor`. The identity retains repeated spatial slots and supplies the entry data for cumulant norm estimates. Neither isotropy of $\mu$ nor centering or unit variance of $f$ is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem source_mixed_cumulant_entries {n N : ℕ} (hN : 0 < N)
--       (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
--       {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ} (hβ : 0 < β)
--       (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
--       (h110 : β / Real.sqrt N * M ≤ a)
--       {d : ℕ} (hd : 1 ≤ d) (I : Fin d → Fin N) (J : Fin d → Fin n) :
--       cumulant (jointLaw (hV.law : Measure _) f β (sigma β) N) (d + 1)
--         (Fin.cons (EuclideanSpace.single none 1)
--           (fun k => EuclideanSpace.single (some (I k, J k)) 1)) =
--         if ∀ k k', I k = I k' then
--           (d.factorial : ℝ) / (sigma β * Real.sqrt N) *
--             taylorTensor (hV.law : Measure _) f d
--               (fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) else 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Derivatives`](https://prove2.me/theorems/3fa39843-9f8d-446f-806f-25b47f8ada2b).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`contDiffOn_logLaplace_ball`](https://prove2.me/theorems/dd1e2494-e9a9-46a2-a434-95c8dca4c3ef), [`exists_integrable_exp_norm`](https://prove2.me/theorems/cae54259-25c9-4b6d-b8ab-140080dd2348), [`fderiv_logLaplace_jointLaw_none`](https://prove2.me/theorems/c111409b-45db-45b0-903a-b9f1a6b86e12), [`jointLaw_eq_tilted`](https://prove2.me/theorems/a3adf66f-9b93-4f82-ab91-3e0f0b7f991d), [`logConcave_jointLaw_of_eq_tilted`](https://prove2.me/theorems/91e4e9b1-0b51-481d-b310-130f8697a3a8).
--
--   Previous: [`fderiv_logLaplace_jointLaw_none`](https://prove2.me/theorems/c111409b-45db-45b0-903a-b9f1a6b86e12).
--
--   [Source excerpt, lines 713–725](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean#L713-L725) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean#L711-L790 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Derivatives`, declaration `_private.FunctionalInequalities.KLS.BKL.Suspension.Derivatives.0.FunctionalInequalities.KLS.LogConcave.Suspension.source_mixed_cumulant_entries`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
set_option autoImplicit false

theorem FunctionalInequalities.KLS.LogConcave.Suspension.source_mixed_cumulant_entries_readable {n N : ℕ} (hN : 0 < N)
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ} (hβ : 0 < β)
    (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (h110 : β / Real.sqrt N * M ≤ a)
    {d : ℕ} (hd : 1 ≤ d) (I : Fin d → Fin N) (J : Fin d → Fin n) :
    cumulant (jointLaw (hV.law : Measure _) f β (sigma β) N) (d + 1)
      (Fin.cons (EuclideanSpace.single none 1)
        (fun k => EuclideanSpace.single (some (I k, J k)) 1)) =
      if ∀ k k', I k = I k' then
        (d.factorial : ℝ) / (sigma β * Real.sqrt N) *
          taylorTensor (hV.law : Measure _) f d
            (fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) else 0 := by sorry
