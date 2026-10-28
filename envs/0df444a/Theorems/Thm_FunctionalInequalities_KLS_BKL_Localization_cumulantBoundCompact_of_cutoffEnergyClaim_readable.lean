-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cumulantBoundCompact_of_cutoffEnergyClaim_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.cumulantBoundCompact_of_cutoffEnergyClaim_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:52.968099+00:00
-- url     : https://prove2.me/theorems/a3ff251c-553e-44e1-9529-aa9e7643ca87
-- title:
--   Cumulant Bound From the Cutoff Energy Claim
-- statement:
--   This formalizes the cutoff-to-cumulant implication associated with the cumulant bounds in Theorem 4.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 18.
--
--   Let $K\in\mathbb R$ satisfy $0\le K$, and let $d\in\mathbb N$. Assume `CutoffEnergyClaim K d`. Then the compact cumulant bound holds with parameter `envelope K (d + 1)`:
--
--   $$\operatorname{CumulantBoundCompact}\bigl(d,\operatorname{envelope}(K,d+1)\bigr).$$
--
--   The definition `CumulantBoundCompact` quantifies over finite dimensions, isotropic log-concave probability measures, compact-support hypotheses, and vectors $u$, and bounds the corresponding sum of squared cumulants by
--
--   $$\operatorname{envelope}(K,d+1)\,\lVert u\rVert^2.$$
--
--   This declaration is an auxiliary interface converting the stated cutoff-energy hypothesis into the compact cumulant-bound formulation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulantBoundCompact_of_cutoffEnergyClaim {K : ℝ} (hK : 0 ≤ K) {d : ℕ} (h : CutoffEnergyClaim K d) :
--       LogConcave.Suspension.CumulantBoundCompact d (envelope K (d + 1))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CutoffEnergy/ToCumulant`](https://prove2.me/theorems/666be960-e15a-411c-8bcf-4b291f3f4182).
--
--   Definition modules: [`KLS/BKL/Localization/CutoffEnergy/Basic`](https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b), [`KLS/BKL/CumulantEnvelope`](https://prove2.me/theorems/dd70df63-9b7a-4c42-ab12-35ef642d8be7), [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Supporting theorems: [`exists_isEldanCutoff`](https://prove2.me/theorems/c19ca091-9b2b-4723-a463-2678e5d1f088), [`IsBrownianFiltration.rightCont`](https://prove2.me/theorems/78df4d86-f7fc-4e75-a946-edef2afd609d), [`MultidimBrownianMotion.exists`](https://prove2.me/theorems/7d8b284a-c9b3-4927-9d3c-74473785d55c), [`isBrownianFiltration_natural`](https://prove2.me/theorems/55e5bfed-69f0-42a9-b549-d693f92f0fd1).
--
--   [Source excerpt, lines 47–48](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/ToCumulant.lean#L47-L48) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/ToCumulant.lean#L45-L191 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.ToCumulant`, declaration `FunctionalInequalities.KLS.BKL.Localization.cumulantBoundCompact_of_cutoffEnergyClaim`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_ToCumulant

theorem FunctionalInequalities.KLS.BKL.Localization.cumulantBoundCompact_of_cutoffEnergyClaim_readable {K : ℝ} (hK : 0 ≤ K) {d : ℕ} (h : CutoffEnergyClaim K d) :
    LogConcave.Suspension.CumulantBoundCompact d (envelope K (d + 1)) := by sorry
