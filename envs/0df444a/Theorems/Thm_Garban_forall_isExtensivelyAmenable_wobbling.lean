-- Prove2me | Theorems.Thm_Garban_forall_isExtensivelyAmenable_wobbling
-- name    : Garban.forall_isExtensivelyAmenable_wobbling
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-07T09:31:05.650985+00:00
-- url     : https://prove2.me/theorems/7d559217-d348-4abc-a109-27c1e9224d61
-- title:
--   Garban's question — W(ℤ^d) ↷ ℤ^d is extensively amenable for every d (open)
-- statement:
--   For every $d \ge 0$, the action of the wobbling group $W(\mathbf Z^d)$, the permutations $\sigma$ of $\mathbf Z^d$ with $\sup_x d(\sigma x, x) < \infty$, on $\mathbf Z^d$ is extensively amenable.
--
--   Garban, p. 1: “The recent breakthrough works [9, 11, 12] which established the amenability for new classes of groups, lead to the following question: is the action $W(\mathbb Z^d) \curvearrowright \mathbb Z^d$ extensively amenable? (Where $W(\mathbb Z^d)$ is the wobbling group of permutations $\sigma : \mathbb Z^d \to \mathbb Z^d$ with bounded range). This is equivalent to asking whether the action $(\mathbb Z/2\mathbb Z)^{(\mathbb Z^d)} \rtimes W(\mathbb Z^d) \curvearrowright (\mathbb Z/2\mathbb Z)^{(\mathbb Z^d)}$ is amenable. The $d = 1$ and $d = 2$ and have been settled respectively in [9, 11].”
--
--   The question is open. Juschenko and de la Salle (p. 2) call the case $d \ge 3$ “an intriguing open question”, and Garban conjectures a negative answer for $d \ge 3$ (p. 1); a disproof is as welcome as a proof. The distance on $\mathbf Z^d$ is the sup distance; bounded range is the same for the graph distance.
-- source:
--   Garban, C., Inverted orbits of exclusion processes, diffuse-extensive-amenability, and (non-?)amenability of the interval exchanges, Groups Geom. Dyn. 14 (2020) 871–897, https://doi.org/10.4171/GGD/567 (arXiv:1804.01981v4, whose page numbers are used), p. 1, the abstract (open), and Juschenko, K. and de la Salle, M., Invariant means for the wobbling group, Bull. Belg. Math. Soc. Simon Stevin 22 (2015) 281–290, https://doi.org/10.36045/bbms/1432840864 (arXiv:1301.4736v4, whose page numbers are used), p. 2

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace Garban

theorem forall_isExtensivelyAmenable_wobbling (d : ℕ) :
    IsExtensivelyAmenable ↥(wobbling (Fin d → ℤ)) (Fin d → ℤ) := by
  sorry

end Garban
