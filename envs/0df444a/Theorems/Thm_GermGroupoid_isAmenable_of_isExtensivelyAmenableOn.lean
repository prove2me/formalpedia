-- Prove2me | Theorems.Thm_GermGroupoid_isAmenable_of_isExtensivelyAmenableOn
-- name    : GermGroupoid.isAmenable_of_isExtensivelyAmenableOn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T17:11:56.002986+00:00
-- url     : https://prove2.me/theorems/4e9cf8d9-326b-4fa3-bab2-8307e46f6606
-- title:
--   Juschenko–Nekrashevych–de la Salle, extensive amenability form (JMMS Theorem 6.5) — groups of homeomorphisms with germs in an amenable groupoid
-- statement:
--   Let $G$ be a group of homeomorphisms of a topological space $X$ (a subgroup of `X ≃ₜ X`) and let $\mathcal H$ be a groupoid of germs of homeomorphisms of $X$, given by a pseudogroup (`StructureGroupoid X`). Suppose that
--
--   - (i) for every $g \in G$, the germ of $g$ at $x$ belongs to $\mathcal H$ for all but finitely many $x \in X$;
--   - (ii) for every $x \in X$, the group of germs of $G$ at $x$ (`GermGroup G x`) is amenable;
--   - (iii) the action of $G$ on $X$ is extensively amenable (`IsExtensivelyAmenableOn G X Set.univ`);
--   - (iv) the topological full group $[[\mathcal H]]$ (`fullGroup 𝓗`) is amenable.
--
--   Then $G$ is amenable (`Garrido.IsAmenable G`):
--
--   $$\text{(i)} \wedge \text{(ii)} \wedge \text{(iii)} \wedge \text{(iv)} \ \Longrightarrow\ G \text{ is amenable}.$$
--
--   The theorem deduces amenability of a group of homeomorphisms from local data (its germs and their groups) together with one global condition on its orbits.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 23: “Theorem 6.5 ([JNdlS13]). Let $G$ be a group acting on a topological space $X$ with groupoid of germs $\mathcal G$. Assume that there is a groupoid of germs of homeomorphisms $\mathcal H$ acting on $X$ so that the following holds (i) For every $g \in G$ the germ of $g$ at $x$ belongs to $\mathcal H$ for all but finitely many $x \in X$. (ii) For every $x \in X$ the isotropy group $\mathcal G_x$ is amenable. (iii) The action $G \curvearrowright X$ is extensively amenable. (iv) The group $[[\mathcal H]]$ is amenable. Then $G$ is amenable. In fact, condition (iii) in the original statement in [JNdlS13] was that the action is recurrent, but this is used in the proof only through Theorem 4.2.”
--
--   The original is Juschenko, Nekrashevych and de la Salle, Theorem 3.1 (p. 6), for a finitely generated group of homeomorphisms whose orbital Schreier graphs at the singular points are recurrent. Juschenko, Matte Bon, Monod and de la Salle use the theorem to prove their Theorem 6.4, that a subgroup of Monod's group $H$ is amenable if and only if its action on the real line is extensively amenable ([`ThompsonAmenability.isAmenable_iff_isExtensivelyAmenableOn_of_le_Hpp`](https://prove2.me/theorems/4debdb5e-51fb-400a-9b80-e04451b86ceb)).
--
--   **Formalization note.** As in Juschenko, Nekrashevych and de la Salle's Theorem 3.1 (“Let $G$ be a finitely generated group of homeomorphisms of a topological space $\mathcal X$”), $G$ is a group of homeomorphisms, acting on $X$ by evaluation; Theorem 6.5 drops finite generation. The isotropy group $\mathcal G_x$ of the groupoid of germs of $G$ is the stabilizer of $x$ modulo the elements acting trivially near $x$ (JNdlS p. 6). The groupoid of germs $\mathcal H$ is the set of germs of the members of a pseudogroup, and $[[\mathcal H]]$ consists of the homeomorphisms of $X$ all of whose germs lie in it. Extensive amenability is Definition 1.1 of Juschenko, Matte Bon, Monod and de la Salle (`IsExtensivelyAmenableOn`, with $Y = X$), and amenability is the existence of a left-invariant finitely additive probability on all subsets of the group.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 23, Theorem 6.5, which is Juschenko, K., Nekrashevych, V. and de la Salle, M., Extensions of amenable groups by recurrent groupoids, Invent. Math. 206 (2016) 837–867, https://doi.org/10.1007/s00222-016-0664-6 (arXiv:1305.2637v2, whose page numbers are used), p. 6, Theorem 3.1, with extensive amenability in place of recurrence

import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability
import Definitions.Def_HomeomorphAction
import Definitions.Def_GermGroupoid
import Mathlib

namespace GermGroupoid

theorem isAmenable_of_isExtensivelyAmenableOn {X : Type*} [TopologicalSpace X]
    (G : Subgroup (X ≃ₜ X)) (𝓗 : StructureGroupoid X)
    (h1 : ∀ g ∈ G, {x | ¬ GermMem 𝓗 g x}.Finite)
    (h2 : ∀ x, Garrido.IsAmenable (GermGroup G x))
    (h3 : ThompsonAmenability.IsExtensivelyAmenableOn G X Set.univ)
    (h4 : Garrido.IsAmenable (fullGroup 𝓗)) :
    Garrido.IsAmenable G := by
  sorry

end GermGroupoid
