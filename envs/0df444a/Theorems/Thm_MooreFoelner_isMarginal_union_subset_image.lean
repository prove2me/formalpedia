-- Prove2me | Theorems.Thm_MooreFoelner_isMarginal_union_subset_image
-- name    : MooreFoelner.isMarginal_union_subset_image
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:04:48.841791+00:00
-- url     : https://prove2.me/theorems/74bcffe0-6ed2-4b2e-8fd4-819905302ba1
-- title:
--   Remark 3.8 — finite unions, subsets and translates of marginal sets are marginal
-- statement:
--   For a partial action of $G$ on $S$: a finite union of marginal sets is marginal; a subset of a marginal set is marginal; for $E \subseteq S$ and $g \in G$, $g^{-1}$ marginalizes $E \setminus (E \cdot g)$ off $E$; and if $E$ is marginal then so is $E \cdot g$.
--
--   **Formalization Note.** The third clause is stated as Moore writes it, $E \setminus (E \cdot g)$; it holds trivially (take $i = 0$), and $(E \cdot g) \setminus E$ is probably meant. That set is what gives the fourth clause: $g^{-1}$ marginalizes it off $E$ (a point $y \cdot g$ with $y \in E$ is sent back into $E$ by one step of $g^{-1}$), so it is marginal when $E$ is, and $E \cdot g \subseteq E \cup ((E \cdot g) \setminus E)$. This is not one of the four clauses.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 7, Remark 3.8

import Mathlib
import Definitions.Def_MooreFoelner

namespace MooreFoelner

theorem isMarginal_union_subset_image {G S : Type*} [Group G] (act : S → G → Option S)
    (hact : IsPartialAction act) :
    (∀ s : Finset (Set S), (∀ E ∈ s, IsMarginal act E) → IsMarginal act (⋃₀ (s : Set (Set S)))) ∧
    (∀ E E' : Set S, E' ⊆ E → IsMarginal act E → IsMarginal act E') ∧
    (∀ (E : Set S) (g : G), Marginalizes act g⁻¹ (E \ image act E g) E) ∧
    (∀ (E : Set S) (g : G), IsMarginal act E → IsMarginal act (image act E g)) := by
  sorry

end MooreFoelner
