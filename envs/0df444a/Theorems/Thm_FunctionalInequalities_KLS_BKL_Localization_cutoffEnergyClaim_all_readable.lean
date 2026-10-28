-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffEnergyClaim_all_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_all_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:57.587647+00:00
-- url     : https://prove2.me/theorems/8ed09f22-1ad1-4f50-a5e4-04b6280a1b1e
-- title:
--   All-Order Cutoff Energy Claim
-- statement:
--   This formalizes the strong-induction form of the cutoff-energy claim associated with Equation (95) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Assume the compact Letwin bound and let $K\ge153$. Also assume:
--
--   1. For every $m\ge3$, if the cutoff claims hold at all orders $r-1$ with $2\le r<m$, and the corresponding compact cumulant bounds hold, then `CutoffEnergyClaim K (m - 1)` holds.
--   2. Every `CutoffEnergyClaim K d` implies `CumulantBoundCompact d (envelope K (d+1))`.
--
--   Then every integer $d\ge1$ satisfies
--
--   $$
--   \operatorname{CutoffEnergyClaim}(K,d).
--   $$
--
--   This declaration is an induction interface: it reduces all positive orders to the supplied step and bound hypotheses together with the base case.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cutoffEnergyClaim_all (hL : LogConcave.Suspension.LetwinCompactBound) {K : ℝ} (hK : 153 ≤ K)
--       (hstep : ∀ m : ℕ, 3 ≤ m →
--         (∀ r : ℕ, 2 ≤ r → r < m → CutoffEnergyClaim K (r - 1)) →
--         (∀ r : ℕ, 2 ≤ r → r < m → LogConcave.Suspension.CumulantBoundCompact (r - 1) (envelope K r)) →
--         CutoffEnergyClaim K (m - 1))
--       (hbound : ∀ d : ℕ, CutoffEnergyClaim K d → LogConcave.Suspension.CumulantBoundCompact d (envelope K (d + 1))) :
--       ∀ d : ℕ, 1 ≤ d → CutoffEnergyClaim K d
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CutoffEnergy/Induction`](https://prove2.me/theorems/5d671766-1030-4f35-9cb6-f27dbe9757df).
--
--   Definition modules: [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101), [`KLS/BKL/Localization/CutoffEnergy/Basic`](https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b), [`KLS/BKL/CumulantEnvelope`](https://prove2.me/theorems/dd70df63-9b7a-4c42-ab12-35ef642d8be7).
--
--   Supporting theorems: [`cutoffEnergyClaim_one`](https://prove2.me/theorems/f7a07239-7204-47d5-8070-a43bf7aef41f).
--
--   [Source excerpt, lines 19–25](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Induction.lean#L19-L25) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18; Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (95), p. 25 (proof of Theorem 4.1, Section 6). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Induction.lean#L18-L51 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Induction`, declaration `FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_all`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Induction

theorem FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_all_readable (hL : LogConcave.Suspension.LetwinCompactBound) {K : ℝ} (hK : 153 ≤ K)
    (hstep : ∀ m : ℕ, 3 ≤ m →
      (∀ r : ℕ, 2 ≤ r → r < m → CutoffEnergyClaim K (r - 1)) →
      (∀ r : ℕ, 2 ≤ r → r < m → LogConcave.Suspension.CumulantBoundCompact (r - 1) (envelope K r)) →
      CutoffEnergyClaim K (m - 1))
    (hbound : ∀ d : ℕ, CutoffEnergyClaim K d → LogConcave.Suspension.CumulantBoundCompact d (envelope K (d + 1))) :
    ∀ d : ℕ, 1 ≤ d → CutoffEnergyClaim K d := by sorry
