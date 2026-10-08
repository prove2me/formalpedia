-- Prove2me | Theorems.Thm_KelsoCrawford_CompStatics_nfb_converges_firm_optimal
-- name    : KelsoCrawford.CompStatics.nfb_converges_firm_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:09.725405+00:00
-- url     : https://prove2.me/theorems/eba5f48a-57c3-4943-8c3d-01ee49a3eb72
-- title:
--   Section 5, proof of Theorem 5 — new-firm process reaches a firm-optimal strict core allocation
-- statement:
--   Start from any stopping round of the original market's salary-adjustment process. Keep existing firms' final salaries and offers, and give the entering firm its starting salaries and offers to every worker. Under Theorem 4's conditions in both markets, every legal continuation of this new-firm-on-the-block process stops after finitely many rounds. At every stopping round $S$ its allocation is in the entrant market's discrete strict core, and each firm weakly prefers it to every other discrete strict core allocation $A$:
--
--   $$\forall j,\quad \pi^j(A)\leq\pi^j(A_{\mathrm{NFB},S}).$$
--
--   This is the entrant-side process claim stated in the proof of Theorem 5.
--
--   **Formalization Note** The entrant has firm label `none`; original firms have labels `some j`. NFB1 specifies initial salaries, while this statement fixes the initial offer sets as the original final offers plus offers from the entrant to all workers.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1498, Section 5, proof of Theorem 5, NFB1–NFB5 and ensuing convergence sentence. https://doi.org/10.2307/1913392

import Mathlib
import Definitions.Def_KelsoCrawford_CompStatics_Process

namespace KelsoCrawford.CompStatics

theorem nfb_converges_firm_optimal
    {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (Mplus : Market W (Option F)) (δ : ℝ)
    (hδ : 0 < δ) (hAug : IsFirmAugmentation M Mplus)
    (hM : M.Theorem4Conditions δ)
    (hPlus : Mplus.Theorem4Conditions δ)
    (ρ : Run W F) (hρ : M.IsRun δ ρ)
    (T : ℕ) (hT : ρ.Stopped T)
    (ρNFB : Run W (Option F))
    (hNFB : Mplus.IsRunFrom δ (nfbInitialSalaries Mplus ρ T)
      (nfbInitialOffers ρ T) ρNFB) :
    (∃ S : ℕ, ρNFB.Stopped S) ∧
      ∀ S : ℕ, ρNFB.Stopped S →
        Mplus.IsStrictCore (Mplus.grid δ) (ρNFB.outcome S) ∧
        ∀ A : Allocation W (Option F),
          Mplus.IsStrictCore (Mplus.grid δ) A → ∀ j : Option F,
            KelsoCrawford.OneSided.profit (Mplus.y j) (A.hired j) A.sal ≤
              KelsoCrawford.OneSided.profit (Mplus.y j) ((ρNFB.outcome S).hired j)
                (ρNFB.outcome S).sal := by sorry

end KelsoCrawford.CompStatics
