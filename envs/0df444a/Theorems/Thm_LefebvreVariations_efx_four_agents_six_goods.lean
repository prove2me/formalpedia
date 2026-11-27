-- Prove2me | Theorems.Thm_LefebvreVariations_efx_four_agents_six_goods
-- name    : LefebvreVariations.efx_four_agents_six_goods
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:21:51.624708+00:00
-- url     : https://prove2.me/theorems/4ad0f75a-9b27-4cc1-b165-6d63c13358b2
-- title:
--   Lefebvre's variations, No. 261 — on a theme by Caragiannis, Kurokawa, Moulin, Procaccia, Shah and Wang: four agents with positive additive valuations on six goods admit an EFX allocation
-- statement:
--   Four agents have strictly positive additive valuations $v_i(g)>0$ on six indivisible goods. There is an allocation $f:\{0,\dots,5\}\to\{0,1,2,3\}$ (good $g$ goes to agent $f(g)$) such that every agent $i$ values their own bundle at least as much as any other agent's bundle after removing any single good:
--   $$\forall i,j,\ \forall g\text{ with }f(g)=j:\quad \sum_{h:\,f(h)=j,\ h\ne g}v_i(h)\ \le\ \sum_{h:\,f(h)=i}v_i(h).$$
--
--   The EFX conjecture asserts that for additive valuations such an allocation exists for every number of agents and goods; it is open for four agents and known for three agents. Four agents with six goods, two more goods than agents, is a small four-agent case where an exhaustive search over the $4^6=4096$ allocations is possible.
--
--   **Formalization Note** The allocation is an owner map \texttt{f : Fin 6 $\to$ Fin 4}. The case $i=j$ is included and holds trivially. Strict positivity of the valuations is assumed, so removing any good, including the cheapest, always matters.
--
--   **Why this is a variation.** Small case of the EFX conjecture (existence of EFX allocations for additive valuations, open in general for four or more agents); no open platform problem states it, so there is no formal parent. The statement (four agents, six goods) is, according to a recent preprint citing Mahara for m <= n+3, already a known theorem, so it is offered as a finite explicit statement to be proved, not as an open question. It is not implied by a platform theorem (the proved two-valuation EFX theorem does not cover four distinct valuations). No formal link is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The EFX conjecture: I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah and J. Wang, ACM Trans. Econ. Comput. 7 (2019); existence for three agents: B. R. Chaudhury, J. Garg and K. Mehlhorn, "EFX exists for three agents", EC 2020 (both cited from memory). Existence of complete EFX allocations for m <= n+3 goods with additive valuations is attributed to Mahara (2023) in a 2026 arXiv preprint, "Complete EFX Allocations Exist for Four Additive Agents and Up to Nine Goods" (arXiv 2608.08590, found by web search, not read in full, not peer reviewed), which also claims the case of four agents and up to nine goods by computer-assisted case analysis; the case here (n = 4, m = 6 <= n+3) is therefore believed to be a known theorem, on second-hand evidence. Also checked numerically on 15000 instances (3000 random and 12000 structured), where an EFX allocation was always found.

import Mathlib

namespace LefebvreVariations

/-- Four agents with strictly positive additive valuations on six goods always admit an EFX
allocation. The allocation is an owner map `f : Fin 6 → Fin 4`; EFX means that for all agents
`i`, `j` and every good `g` owned by `j`, agent `i` values their own bundle at least as much as
`j`'s bundle with `g` removed. Source: the EFX conjecture, Caragiannis, Kurokawa, Moulin, Procaccia,
Shah and Wang, ACM Trans. Econ. Comput. 7 (2019); existence for three agents by Chaudhury, Garg
and Mehlhorn (EC 2020), for four agents it is open in general (both cited from memory). -/
theorem efx_four_agents_six_goods (v : Fin 4 → Fin 6 → ℝ) (hv : ∀ i g, 0 < v i g) :
    ∃ f : Fin 6 → Fin 4, ∀ i j g, f g = j →
      ∑ h ∈ Finset.univ.filter (fun h => f h = j ∧ h ≠ g), v i h ≤
        ∑ h ∈ Finset.univ.filter (fun h => f h = i), v i h := by
  sorry

end LefebvreVariations
