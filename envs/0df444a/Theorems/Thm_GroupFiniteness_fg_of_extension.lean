-- Prove2me | Theorems.Thm_GroupFiniteness_fg_of_extension
-- name    : GroupFiniteness.fg_of_extension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T08:49:29.236584+00:00
-- url     : https://prove2.me/theorems/9b78a1d7-7814-4ab9-97e5-fb90e41bbe5e
-- title:
--   An extension of a finitely generated group by a finitely generated group is finitely generated
-- statement:
--   Let $N$ be a normal subgroup of a group $G$ such that both $N$ and the quotient $G/N$ are
--   finitely generated. Then $G$ is finitely generated: a finite generating set is given by a finite
--   generating set of $N$ together with one preimage in $G$ of each element of a finite generating set
--   of $G/N$.
-- source:
--   Standard elementary fact: generators of the normal subgroup together with lifts of generators of the quotient generate the group. Stated here because Mathlib has finite generation of subgroups of finite index (Schreier) and of quotients, but not of extensions.

import Mathlib

namespace GroupFiniteness

/-- An extension of a finitely generated group by a finitely generated group is finitely
generated: generators of `N` together with lifts of generators of `G ⧸ N` generate `G`. -/
theorem fg_of_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [Group.FG N] [Group.FG (G ⧸ N)] : Group.FG G := by
  sorry

end GroupFiniteness
