-- Prove2me | Theorems.Thm_KelsoCrawford_CompStatics_firm_entry_and_worker_exit
-- name    : KelsoCrawford.CompStatics.firm_entry_and_worker_exit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:45.391992+00:00
-- url     : https://prove2.me/theorems/0cd7690e-73bf-4caf-b156-f4830df8ec03
-- title:
--   Theorem 5 — worker gains from firm entry and firm gains from worker presence
-- statement:
--   Let a finite discrete market, its augmentation by one firm, and the market obtained by removing one worker all satisfy Theorem 4's conditions at the same positive salary increment $\delta$. The augmented market agrees with the original on all old firms. Take any legal salary-adjustment run and stopping round in each market. Every original worker is at least as well off after firm entry, measured by utility, and every firm is at least as well off before the worker exits, measured by profit:
--
--   $$\forall i,\quad u_i(A_{\mathrm{original}})\leq u_i(A_{\mathrm{augmented}}),\qquad \forall j,\quad \pi_j(A_{\mathrm{diminished}})\leq\pi_j(A_{\mathrm{original}}).$$
--
--   These are the paper's (FA) and (WD) conclusions. They compare the equilibria selected by the salary-adjustment process, not arbitrary core allocations.
--
--   **Formalization Note** Theorem 4's conditions mean regular utilities, MP, NFL, grid-GS, NTW, and NTF in all three markets. The diminished market excludes the named worker by subtype. No reservation-salary equality is assumed in Section 5. All runs and stopping rounds are quantified explicitly; the Corollary to Theorem 4 ensures the resulting equilibrium is unique.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1497, Theorem 5 (FA), (WD); standing assumptions p. 1486. https://doi.org/10.2307/1913392

import Mathlib
import Definitions.Def_KelsoCrawford_CompStatics_Process

namespace KelsoCrawford.CompStatics

theorem firm_entry_and_worker_exit
    {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (Mplus : Market W (Option F))
    (w₀ : W) (δ : ℝ)
    (hδ : 0 < δ) (hAug : IsFirmAugmentation M Mplus)
    (hM : M.Theorem4Conditions δ)
    (hPlus : Mplus.Theorem4Conditions δ)
    (hMinus : (M.withoutWorker w₀).Theorem4Conditions δ)
    (ρ : Run W F) (ρplus : Run W (Option F))
    (ρminus : Run {i : W // i ≠ w₀} F)
    (hρ : M.IsRun δ ρ) (hρplus : Mplus.IsRun δ ρplus)
    (hρminus : (M.withoutWorker w₀).IsRun δ ρminus)
    (T Tplus Tminus : ℕ)
    (hT : ρ.Stopped T) (hTplus : ρplus.Stopped Tplus)
    (hTminus : ρminus.Stopped Tminus) :
    (∀ i : W,
      M.u i ((ρ.outcome T).assign i) ((ρ.outcome T).sal i) ≤
        Mplus.u i ((ρplus.outcome Tplus).assign i)
          ((ρplus.outcome Tplus).sal i)) ∧
    (∀ j : F,
      KelsoCrawford.OneSided.profit ((M.withoutWorker w₀).y j)
          ((ρminus.outcome Tminus).hired j) (ρminus.outcome Tminus).sal ≤
        KelsoCrawford.OneSided.profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal) := by sorry

end KelsoCrawford.CompStatics
