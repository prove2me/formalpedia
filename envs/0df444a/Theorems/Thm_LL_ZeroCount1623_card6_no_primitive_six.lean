-- Prove2me | Theorems.Thm_LL_ZeroCount1623_card6_no_primitive_six
-- name    : LL_ZeroCount1623.card6_no_primitive_six
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-25T03:54:21.1178+00:00
-- url     : https://prove2.me/theorems/e2990eeb-8a91-4c2c-bc29-db865e35f542
-- title:
--   No primitive Dirichlet character modulo $6$
-- statement:
--   Let $q$ be a nonzero natural number and $\chi$ a Dirichlet character modulo $q$ with values in $\mathbb{C}$. If $q=6$, then $\chi$ is not primitive, that is, its conductor is not $6$.
-- source:
--   Explicit zero count in the major arcs of H. A. Helfgott, The ternary Goldbach problem, arXiv:1501.05438; Lean Lab split of the conductor block 2 to 6.

import Mathlib

namespace LL_ZeroCount1623
theorem card6_no_primitive_six {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q = 6) : ¬ χ.IsPrimitive := by sorry
end LL_ZeroCount1623
