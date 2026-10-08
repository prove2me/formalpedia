-- Prove2me | Theorems.Thm_Garban_isAmenable_IET_of_forall_isExtensivelyAmenable_wobbling
-- name    : Garban.isAmenable_IET_of_forall_isExtensivelyAmenable_wobbling
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T09:30:26.837479+00:00
-- url     : https://prove2.me/theorems/e415e847-a76d-4445-b922-de536ba73635
-- title:
--   Garban, abstract — if W(ℤ^d) ↷ ℤ^d is extensively amenable for every d, then IET is amenable
-- statement:
--   Suppose that for every $d \ge 0$ the action of the wobbling group $W(\mathbf Z^d)$ on $\mathbf Z^d$ is extensively amenable. Then $\mathrm{IET}$ is amenable.
--
--   Here $W(\mathbf Z^d)$ consists of the permutations $\sigma$ of $\mathbf Z^d$ with $\sup_x d(\sigma x, x) < \infty$, for the sup distance on $\mathbf Z^d$; the bounded-range condition is the same for the graph distance of $\mathbf Z^d$ that Garban uses.
--
--   Garban, p. 1: “The recent breakthrough works [9, 11, 12] which established the amenability for new classes of groups, lead to the following question: is the action $W(\mathbb Z^d) \curvearrowright \mathbb Z^d$ extensively amenable? (Where $W(\mathbb Z^d)$ is the wobbling group of permutations $\sigma : \mathbb Z^d \to \mathbb Z^d$ with bounded range). … By [12], a positive answer to this question would imply the amenability of the IET group.” Reference [12] is Juschenko, Matte Bon, Monod and de la Salle.
-- source:
--   Garban, C., Inverted orbits of exclusion processes, diffuse-extensive-amenability, and (non-?)amenability of the interval exchanges, Groups Geom. Dyn. 14 (2020) 871–897, https://doi.org/10.4171/GGD/567 (arXiv:1804.01981v4, whose page numbers are used), p. 1, the abstract

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace Garban

theorem isAmenable_IET_of_forall_isExtensivelyAmenable_wobbling
    (h : ∀ d : ℕ, IsExtensivelyAmenable ↥(wobbling (Fin d → ℤ)) (Fin d → ℤ)) :
    Garrido.IsAmenable ↥IET := by
  sorry

end Garban
