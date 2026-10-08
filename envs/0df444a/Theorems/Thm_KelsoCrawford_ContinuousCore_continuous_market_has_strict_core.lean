-- Prove2me | Theorems.Thm_KelsoCrawford_ContinuousCore_continuous_market_has_strict_core
-- name    : KelsoCrawford.ContinuousCore.continuous_market_has_strict_core
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:54.323735+00:00
-- url     : https://prove2.me/theorems/5de83b1a-d99f-4c9f-be66-489a64037264
-- title:
--   Theorem 2 — every continuous market has a strict core allocation
-- statement:
--   **Theorem 2.** Every continuous market has a strict core allocation.
--
--   Let $W$ and $F$ be finite sets of workers and firms, with at least one firm. Suppose each utility $u^i(j;\cdot)$ is strictly increasing and continuous, the technologies satisfy (MP) and (NFL), the reservation salaries satisfy $u^i(j;\sigma_{ij})=u^i(k;\sigma_{ik})$ for all $i,j,k$ (all equal to the utility of unemployment), and every firm satisfies (GS) on all real salary vectors. Then there is an individually rational allocation $(f;s_{1f(1)},\dots,s_{mf(m)})$ such that no firm $j$, set of workers $C$ and real salaries $r_{ij}$ satisfy
--
--   $$u^i(j;r_{ij})\ge u^i\big(f(i);s_{if(i)}\big)\ (i\in C)\quad\text{and}\quad\pi^j(C;r^j)\ge\pi^j(C^j;s^j)$$
--
--   with strict inequality for at least one member of $C\cup\{j\}$ (D2).
--
--   The theorem gives existence of a stable assignment of workers to firms with endogenous firm sizes, for any technologies under which workers are gross substitutes; with one worker per firm and additively separable utility it contains the Shapley–Shubik assignment game.
--
--   **Formalization Note** "Continuous market" means that coalitions may use any real salaries. The conclusion is the strict core (D2), not the weaker core (D3). The standing assumptions of Section 2 (p. 1486), which the theorem's sentence does not repeat, are hypotheses; at least one firm is assumed (the paper's $n\ge1$), since with no firms and some worker no allocation exists.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1490, Theorem 2

import Mathlib
import Definitions.Def_KelsoCrawford_ContinuousCore_Model

namespace KelsoCrawford.ContinuousCore

theorem continuous_market_has_strict_core {W F : Type}
    [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hres : M.ReservationSalaries)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) Set.univ) :
    ∃ A : Allocation W F, M.IsStrictCore anySalary A := by sorry

end KelsoCrawford.ContinuousCore
