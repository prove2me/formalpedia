-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_theorem_1
-- name    : OptInapprox.MaxCut.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:28:58.870987+00:00
-- url     : https://prove2.me/theorems/b4e6f839-fb0d-43a7-a64d-356e849bbc37
-- title:
--   Theorem 1, p. 11 — assuming the UGC, (1/2 − ρ/2)- vs ((arccos ρ)/π + ε)-satisfiable MAX-CUT is NP-hard to distinguish
-- statement:
--   Assume the Unique Games Conjecture (and the Majority Is Stablest theorem of [45]). Then for every constant $-1<\rho<0$ and $\epsilon>0$, it is NP-hard to distinguish instances of MAX-CUT that are at least
--   $$\Big(\tfrac12-\tfrac12\rho\Big)\text{-satisfiable}$$
--   from instances that are at most $\big(\tfrac{\arccos\rho}{\pi}+\epsilon\big)$-satisfiable.
--
--   Taking $\rho$ to minimize the ratio of the two thresholds shows that, under the UGC, MAX-CUT cannot be approximated in polynomial time within any factor greater than the Goemans–Williamson constant $\alpha_{GW}\approx0.878567$ unless P = NP.
--
--   **Formalization Note.**
--   1. The Unique Games Conjecture is the hypothesis `UGC`. The proof also uses the Majority Is Stablest theorem, which the paper cites as proved in [45] and does not prove; it enters as the second hypothesis `MajorityIsStablest`.
--   2. Instances are loopless graphs with natural-number edge weights (edge multiplicities), as §7.1 allows. Both promise sets require at least one edge.
--   3. "NP-hard to distinguish" is `GapNPHard` over one-tape Turing machines. For large $\epsilon$ the two promise sets overlap; the statement is then still the page's, only weaker.
--   4. The "In particular" sentence about $\rho^*$ and $\alpha_{GW}$ is not part of this statement.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 11, Theorem 1

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_MIS
import Definitions.Def_OptInapprox_MaxCut_UGC

namespace OptInapprox.MaxCut

theorem theorem_1 (hUGC : UGC) (hMIS : MajorityIsStablest) (ρ ε : ℝ) (hρ₁ : -1 < ρ)
    (hρ₂ : ρ < 0) (hε : 0 < ε) :
    GapNPHard encMaxCut
      (fun G : WMaxCut => G.edges ≠ [] ∧ ∃ c, 1 / 2 - ρ / 2 ≤ G.cutFrac c)
      (fun G : WMaxCut => G.edges ≠ [] ∧ ∀ c, G.cutFrac c ≤ Real.arccos ρ / Real.pi + ε) := by sorry

end OptInapprox.MaxCut
