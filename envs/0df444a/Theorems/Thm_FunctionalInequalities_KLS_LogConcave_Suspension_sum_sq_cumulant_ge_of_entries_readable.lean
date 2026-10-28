-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_sum_sq_cumulant_ge_of_entries_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.sum_sq_cumulant_ge_of_entries_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:42.874552+00:00
-- url     : https://prove2.me/theorems/2c0417e5-0964-49ff-aaed-cde1424459aa
-- title:
--   Cumulant Slice Lower Bound From Prescribed Mixed Entries
-- statement:
--   This auxiliary statement formalizes the Hilbert–Schmidt lower-bound component of Proposition 7.1, p. 28, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), associated with equation (112).
--
--   Let $n,N,d\in\mathbb N$ with $N>0$ and $d\ge1$, and $\sigma>0$. Let $\mu$ be any measure on $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), $f:E\to\mathbb R$, and $\nu$ any measure on $H=$ `JointSpace` $N\ n$, whose coordinate set is $Q=\operatorname{Option}(\operatorname{Fin}N\times\operatorname{Fin}n)$. Denote the coordinate unit vectors by $e_0$ and $e_{(i,j)}$, and the standard basis of $E$ by $b_j$. Write $\kappa_{d+1}^\nu=$ `cumulant` $\nu\ (d+1)$ and $T_d^\mu f=$ `taylorTensor` $\mu\ f\ d$.
--
--   Assume, for every $I:\operatorname{Fin}d\to\operatorname{Fin}N$ and $J:\operatorname{Fin}d\to\operatorname{Fin}n$,
--   $$
--   \kappa_{d+1}^\nu(e_0,e_{(I_k,J_k)}:k\in\operatorname{Fin}d)=
--   \begin{cases}
--   \dfrac{d!}{\sigma\sqrt N}T_d^\mu f(b_{J_k}:k\in\operatorname{Fin}d),& I\text{ is constant},\\
--   0,&\text{otherwise}.
--   \end{cases}
--   $$
--   Then, with $\operatorname{coord}$ denoting `coordTensor` in the basis $(b_j)$,
--   $$
--   \frac{(d!)^2}{\sigma^2}\|\operatorname{coord}(T_d^\mu f)\|^2
--   \le\sum_{K:\operatorname{Fin}d\to Q}\bigl[\kappa_{d+1}^\nu(e_0,e_{K_k}:k\in\operatorname{Fin}d)\bigr]^2.
--   $$
--
--   This converts the assumed entry identities into a norm lower bound. No probability, integrability, isotropy, or log-concavity hypotheses are imposed on the measures.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_sq_cumulant_ge_of_entries {n N : ℕ} (hN : 0 < N) (ν : Measure (JointSpace N n))
--       (μ : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ) {σ : ℝ} (hσ : 0 < σ)
--       {d : ℕ} (hd : 1 ≤ d)
--       (h112 : ∀ (I : Fin d → Fin N) (J : Fin d → Fin n),
--         cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
--             EuclideanSpace.single (some (I k, J k)) 1) =
--           if ∀ k k', I k = I k' then
--             (d.factorial : ℝ) / (σ * Real.sqrt N) *
--               taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)
--           else 0) :
--       (d.factorial : ℝ) ^ 2 / σ ^ 2 *
--           ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ f d)‖ ^ 2 ≤
--         ∑ K : Fin d → Option (Fin N × Fin n),
--           cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
--             EuclideanSpace.single (K k) 1) ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Cumulant`](https://prove2.me/theorems/01ff1334-f332-41dc-ab58-0fb2ead9dd7b).
--
--   Definition modules: [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`sum_sq_blocks_le`](https://prove2.me/theorems/4c57808a-480e-483b-b687-b1b06f6ba0cf).
--
--   Next: [`lintegral_exp_inner_jointLaw`](https://prove2.me/theorems/ca4eae99-414a-4309-a1fd-64651f80b00f).
--
--   [Source excerpt, lines 30–44](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L30-L44) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean#L29-L65 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Cumulant`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.sum_sq_cumulant_ge_of_entries`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor

theorem FunctionalInequalities.KLS.LogConcave.Suspension.sum_sq_cumulant_ge_of_entries_readable {n N : ℕ} (hN : 0 < N) (ν : Measure (JointSpace N n))
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ) {σ : ℝ} (hσ : 0 < σ)
    {d : ℕ} (hd : 1 ≤ d)
    (h112 : ∀ (I : Fin d → Fin N) (J : Fin d → Fin n),
      cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (some (I k, J k)) 1) =
        if ∀ k k', I k = I k' then
          (d.factorial : ℝ) / (σ * Real.sqrt N) *
            taylorTensor μ f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)
        else 0) :
    (d.factorial : ℝ) ^ 2 / σ ^ 2 *
        ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ f d)‖ ^ 2 ≤
      ∑ K : Fin d → Option (Fin N × Fin n),
        cumulant ν (d + 1) (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (K k) 1) ^ 2 := by sorry
