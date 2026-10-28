-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffEnergyClaim_succ_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_succ_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:44.734268+00:00
-- url     : https://prove2.me/theorems/8ae5977b-ab49-4d46-8c59-295ce589f83a
-- title:
--   Inductive Step for the Cutoff Energy Claim
-- statement:
--   This formalizes the inductive step for the cutoff version of BKL Section 6, including Equation (95), p. 25.
--
--   Assume the compact Letwin bound and the formal hypothesis `Lemma51Bound`. Let $K\ge153$, let $m\ge3$, and suppose that for every $r$ with $2\le r<m$ both the cutoff claim at order $r-1$ and the compact posterior cumulant bound at order $r-1$ with constant $\operatorname{envelope}(K,r)$ hold. Then the cutoff claim holds at order $m-1$:
--
--   $$
--   \operatorname{CutoffEnergyClaim}(K,m-1).
--   $$
--
--   The statement is an inductive implication, not a standalone universal cumulant theorem. It combines the previously assumed lower-order cutoff and cumulant estimates with the named compact-support and generator hypotheses.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cutoffEnergyClaim_succ (hL : LogConcave.Suspension.LetwinCompactBound) (h51 : Lemma51Bound)
--       {K : ℝ} (hK : 153 ≤ K) {m : ℕ} (hm : 3 ≤ m)
--       (ih : ∀ r : ℕ, 2 ≤ r → r < m → CutoffEnergyClaim K (r - 1))
--       (ihb : ∀ r : ℕ, 2 ≤ r → r < m → LogConcave.Suspension.CumulantBoundCompact (r - 1) (envelope K r)) :
--       CutoffEnergyClaim K (m - 1)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CutoffEnergy/Step`](https://prove2.me/theorems/6083b927-e2d3-45a6-af55-38d3d9d080a5).
--
--   Definition modules: [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101), [`KLS/BKL/Localization/CutoffEnergy/Basic`](https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b), [`KLS/BKL/CumulantEnvelope`](https://prove2.me/theorems/dd70df63-9b7a-4c42-ab12-35ef642d8be7).
--
--   Selected supporting theorems: [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`IsEldanCutoff.ae_Q_posSemidef`](https://prove2.me/theorems/adbc9c5b-5b86-46cc-9924-be91f135d845), [`IsEldanCutoff.continuous`](https://prove2.me/theorems/3156d5a3-dbca-44fb-850e-0592de8c55d8), [`IsEldanCutoff.exists_weighted_energy_le`](https://prove2.me/theorems/0093b479-64bc-4ff4-8d31-2c2c61eec957), [`IsEldanCutoff.integrable_integral_of_ae_bound`](https://prove2.me/theorems/00d79fdf-b844-4072-9e3f-f54285d97844).
--
--   [Source excerpt, lines 181–185](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Step.lean#L181-L185) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18; Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (95), p. 25 (proof of Theorem 4.1, Section 6). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Step.lean#L177-L383 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Step`, declaration `FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_succ`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Step

set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_succ_readable (hL : LogConcave.Suspension.LetwinCompactBound) (h51 : Lemma51Bound)
    {K : ℝ} (hK : 153 ≤ K) {m : ℕ} (hm : 3 ≤ m)
    (ih : ∀ r : ℕ, 2 ≤ r → r < m → CutoffEnergyClaim K (r - 1))
    (ihb : ∀ r : ℕ, 2 ≤ r → r < m → LogConcave.Suspension.CumulantBoundCompact (r - 1) (envelope K r)) :
    CutoffEnergyClaim K (m - 1) := by sorry
