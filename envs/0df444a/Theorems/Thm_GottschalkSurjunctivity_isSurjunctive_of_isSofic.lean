-- Prove2me | Theorems.Thm_GottschalkSurjunctivity_isSurjunctive_of_isSofic
-- name    : GottschalkSurjunctivity.isSurjunctive_of_isSofic
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T17:00:50.463235+00:00
-- url     : https://prove2.me/theorems/c1159d0e-bbe4-4c76-9715-0d518c717442
-- title:
--   Sofic groups are surjunctive (Gromov, Weiss)
-- statement:
--   **Theorem (Gromov 1999; Weiss 2000).** Every sofic group is surjunctive. Here $G$ is sofic if for every finite $K\subseteq G$ and every $\varepsilon>0$ there are a finite nonempty set $X$ and a map $\sigma : G\to\mathrm{Sym}(X)$ such that $\sigma_{gh}$ and $\sigma_g\sigma_h$ agree on at least $(1-\varepsilon)|X|$ points for all $g,h\in K$, and $\sigma_g$ moves at least $(1-\varepsilon)|X|$ points for every $g \in K\setminus\{1\}$.
--
--   This is the strongest known general result towards the conjecture; sofic groups include all amenable and all residually finite groups.
-- source:
--   M. Gromov, Endomorphisms of symbolic algebraic varieties, J. Eur. Math. Soc. 1 (1999) 109-197, https://doi.org/10.1007/PL00011162; B. Weiss, Sofic groups and dynamical systems, Sankhya Ser. A 62 (2000) 350-359

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

namespace GottschalkSurjunctivity

theorem isSurjunctive_of_isSofic (G : Type) [Group G]
    (hG : IsSofic G) : IsSurjunctive G := by sorry

end GottschalkSurjunctivity
