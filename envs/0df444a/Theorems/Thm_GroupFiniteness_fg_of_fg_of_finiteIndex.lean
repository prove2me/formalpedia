-- Prove2me | Theorems.Thm_GroupFiniteness_fg_of_fg_of_finiteIndex
-- name    : GroupFiniteness.fg_of_fg_of_finiteIndex
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T17:06:57.261781+00:00
-- url     : https://prove2.me/theorems/a36a9ee9-4cee-41b8-aec3-0d7d6296076b
-- title:
--   A group with a finitely generated subgroup of finite index is finitely generated
-- statement:
--   Let $H$ be a subgroup of finite index in a group $G$, and suppose that $H$ is finitely
--   generated. Then $G$ is finitely generated.
--
--   Nothing is asserted about the number of generators: the conclusion is the bare existence of a
--   finite generating set. One can be obtained by taking a finite generating set of $H$ together with
--   one representative of each of the finitely many cosets of $H$, since every $g \in G$ is the
--   representative of its own coset times an element of $H$. The subgroup is not assumed normal.
-- source:
--   The converse of Schreier's lemma. Mathlib has Schreier's lemma itself, `Subgroup.fg_of_index_ne_zero`: a subgroup of finite index in a finitely generated group is finitely generated. It does not have this direction, which is needed wherever a property is transferred from a finite-index subgroup to the whole group, as in Wolf's Proposition 4.1.

import Mathlib

namespace GroupFiniteness

theorem fg_of_fg_of_finiteIndex {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] [Group.FG H] : Group.FG G := by
  sorry

end GroupFiniteness
