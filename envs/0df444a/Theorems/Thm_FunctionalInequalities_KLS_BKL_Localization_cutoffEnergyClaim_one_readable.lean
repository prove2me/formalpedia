-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffEnergyClaim_one_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_one_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:24.444722+00:00
-- url     : https://prove2.me/theorems/f7a07239-7204-47d5-8070-a43bf7aef41f
-- title:
--   Base Cutoff Energy Claim
-- statement:
--   This formalizes the base case $m=2$ cited in the discussion following Equation (78) and in Equation (95) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Assume the compact Letwin bound `LetwinCompactBound`. For every real $K\ge5$, the cutoff-energy proposition `CutoffEnergyClaim K 1` holds:
--
--   $$
--   \operatorname{LetwinCompactBound}\ \Longrightarrow\ K\ge5\ \Longrightarrow\ \operatorname{CutoffEnergyClaim}(K,1).
--   $$
--
--   The proposition packages the base-order energy inequality, with all of its internal quantification over compactly supported isotropic log-concave laws, unit vectors, cutoffs, and Eldan-process data. It is a base case for the subsequent induction.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cutoffEnergyClaim_one (hL : LogConcave.Suspension.LetwinCompactBound) {K : ℝ} (hK : 5 ≤ K) :
--       CutoffEnergyClaim K 1
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CutoffEnergy/Base`](https://prove2.me/theorems/a9cb3769-8222-4e2c-854f-6ec49449b8d2).
--
--   Definition modules: [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101), [`KLS/BKL/Localization/CutoffEnergy/Basic`](https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b).
--
--   Selected supporting theorems: [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`IsEldanCutoff.ae_Q_posSemidef`](https://prove2.me/theorems/adbc9c5b-5b86-46cc-9924-be91f135d845), [`IsEldanCutoff.continuous`](https://prove2.me/theorems/3156d5a3-dbca-44fb-850e-0592de8c55d8), [`IsEldanCutoff.dynkin`](https://prove2.me/theorems/4bc350bc-15db-49c9-826f-42946b8cb2ba), [`IsEldanCutoff.integrable_integral_of_ae_bound`](https://prove2.me/theorems/00d79fdf-b844-4072-9e3f-f54285d97844).
--
--   Previous: [`cumulantEnergy_one_is_one`](https://prove2.me/theorems/ccab3cfd-b307-417a-bd30-430ee74f8d2d).
--
--   [Source excerpt, lines 119–120](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Base.lean#L119-L120) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18; Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (95), p. 25 (proof of Theorem 4.1, Section 6). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Base.lean#L117-L255 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Base`, declaration `FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_one`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Base

theorem FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_one_readable (hL : LogConcave.Suspension.LetwinCompactBound) {K : ℝ} (hK : 5 ≤ K) :
    CutoffEnergyClaim K 1 := by sorry
