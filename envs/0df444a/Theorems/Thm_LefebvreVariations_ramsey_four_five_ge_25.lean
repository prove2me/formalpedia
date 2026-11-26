-- Prove2me | Theorems.Thm_LefebvreVariations_ramsey_four_five_ge_25
-- name    : LefebvreVariations.ramsey_four_five_ge_25
-- status  : Proved
-- author  : @Secousses
-- created : 2026-11-24T23:14:39.411635+00:00
-- url     : https://prove2.me/theorems/85db69e1-1494-4dca-9acb-8aedce9ca397
-- title:
--   Lefebvre's variations, No. 43 — on a theme by Ramsey: the lower bound $R(4,5)\ge 25$
-- statement:
--   This is the lower bound $R(4,5)\ge25$ for the asymmetric Ramsey number.
--
--   There is a graph on $24$ vertices with no clique of size $4$ and no independent set of size $5$; therefore $R(4,5)\ge25$.
--
--   A witness is the circulant graph on $\mathbb Z/24\mathbb Z$ in which $i$ and $j$ are adjacent when $i-j\in\pm\{1,2,4,8,9\}$. The absence of $4$-cliques and of independent $5$-sets is verified by exhaustive search over all $4$-subsets and $5$-subsets, and any smaller number of vertices is handled by taking induced subgraphs.
--
--   McKay and Radziszowski showed $R(4,5)=25$; the lower bound is due to Kalbfleisch (1965).
--
--   **Formalization Note** $R(4,5)$ is the mission's `Erdos77.asymmetricRamsey 4 5`, the least $n$ such that every graph on at least $n$ vertices has a $4$-clique or an independent $5$-set; it is shown to be well defined by the standard recursion $R(a,b)\le R(a-1,b)+R(a,b-1)$.
--
--   **Why this is a variation.** This varies the open Prove2Me statement `RamseyValues.ramsey_four_five`, that $R(4,5)=25$. It is the lower half of the parent: $R(4,5)\ge 25$, witnessed by an explicit circulant graph on $24$ vertices with no $K_4$ and no independent $5$-set. Settling it gives one of the two inequalities whose combination is the parent equality, leaving only the upper bound $R(4,5)\le 25$.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. G. Kalbfleisch, Construction of special edge-chromatic graphs, Canad. Math. Bull. 8 (1965), 575–584 (lower bound R(4,5) ≥ 25); upper bound and exact value: B. D. McKay and S. P. Radziszowski, R(4,5) = 25, J. Graph Theory 19 (1995), 309–322. Survey: S. P. Radziszowski, Small Ramsey Numbers, Electron. J. Combin., Dynamic Survey DS1. Parent problem: RamseyValues.ramsey_four_five.

import Definitions.Def_Erdos77_asymmetric_ramsey

set_option autoImplicit false

namespace LefebvreVariations

/-- Lower half of `RamseyValues.ramsey_four_five`: `R(4,5) ≥ 25`.  Witness: the circulant graph
on `ℤ/24` with connection set `±{1, 2, 4, 8, 9}` has no `K₄` and no independent 5-set
(Kalbfleisch 1965). -/
theorem ramsey_four_five_ge_25 : 25 ≤ Erdos77.asymmetricRamsey 4 5 := by
  sorry

end LefebvreVariations
