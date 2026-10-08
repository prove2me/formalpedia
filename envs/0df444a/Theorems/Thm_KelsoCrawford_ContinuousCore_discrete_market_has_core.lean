-- Prove2me | Theorems.Thm_KelsoCrawford_ContinuousCore_discrete_market_has_core
-- name    : KelsoCrawford.ContinuousCore.discrete_market_has_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:53.749282+00:00
-- url     : https://prove2.me/theorems/0988f264-e034-4ed9-8b33-659b5e15b093
-- title:
--   Section 4 — every discrete market has a core allocation
-- statement:
--   Every discrete market has a core allocation.
--
--   Let $W$ and $F$ be finite sets of workers and firms, with at least one firm, and let the market have strictly increasing continuous utilities $u^i(j;\cdot)$, (MP) and (NFL). Fix a unit $\delta>0$, so that the salaries permitted for the pair $(i,j)$ are $\sigma_{ij},\sigma_{ij}+\delta,\sigma_{ij}+2\delta,\dots$. Suppose every firm satisfies (GS) on its grid salary vectors. Then there is an allocation $(f;s_{1f(1)},\dots,s_{mf(m)})$ that is individually rational, pays every worker a permitted salary, and cannot be strictly improved upon (D3) by any firm $j$, set of workers $C$ and permitted salaries $r_{ij}$:
--
--   $$\neg\Big(u^i(j;r_{ij})>u^i\big(f(i);s_{if(i)}\big)\ \forall i\in C\ \text{ and }\ \pi^j(C;r^j)>\pi^j(C^j;s^j)\Big).$$
--
--   The paper obtains this from Theorem 1 (the salary-adjustment process converges to a discrete core allocation); the proof of Theorem 2 uses it with a unit small enough to reach a contradiction.
--
--   **Formalization Note** This is the existence statement only; the process R1–R5 is not encoded. (GS) is required only on the grid, as the paper remarks on p. 1487 that a discrete market may satisfy (GS) while its continuous version does not. The reservation-salary link $u^i(j;\sigma_{ij})=u^i(0;0)$ is not assumed: the existence argument does not use it.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1490, Section 4, paragraph immediately before Theorem 2

import Mathlib
import Definitions.Def_KelsoCrawford_ContinuousCore_Model

namespace KelsoCrawford.ContinuousCore

theorem discrete_market_has_core {W F : Type}
    [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (δ : ℝ) (hδ : 0 < δ)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) :
    ∃ A : Allocation W F, M.IsCore (M.grid δ) A := by sorry

end KelsoCrawford.ContinuousCore
