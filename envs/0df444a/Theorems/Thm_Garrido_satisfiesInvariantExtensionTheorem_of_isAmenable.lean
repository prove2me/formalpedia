-- Prove2me | Theorems.Thm_Garrido_satisfiesInvariantExtensionTheorem_of_isAmenable
-- name    : Garrido.satisfiesInvariantExtensionTheorem_of_isAmenable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T22:40:17.684352+00:00
-- url     : https://prove2.me/theorems/fd60b45e-ed19-46cb-8614-20884bd62a75
-- title:
--   Garrido, Theorem 2.6 — an amenable group satisfies the Invariant Extension Theorem for every boolean algebra
-- statement:
--   If $G$ is amenable (`Garrido.IsAmenable G`), then $G$ satisfies the Invariant Extension Theorem (`SatisfiesInvariantExtensionTheorem G`): whenever $G$ acts by automorphisms on a boolean algebra $\mathcal A$, a finitely additive measure $\mu$ on a $G$-invariant subring $\mathcal R$ that is itself $G$-invariant extends to a finitely additive measure $\bar\mu$ on all of $\mathcal A$ with $\bar\mu(g a) = \bar\mu(a)$ for every $g \in G$ and $a \in \mathcal A$.
--
--   Garrido writes on p. 7: “**Theorem 2.6** (Invariant Extension Theorem). *Recall Carathéodory’s Extension Theorem: If $\mathcal R$ is a subring of the boolean algebra $\mathcal A$ and $\mu$ is a measure on $\mathcal R$, then $\mu$ can be extended to a measure $\bar\mu$ on $\mathcal A$.* *If $G$ is an amenable group of automorphisms of $\mathcal A$ and $\mathcal R$, $\mu$ are $G$-invariant, then $\bar\mu$ can be chosen to be $G$-invariant.*” This is the second sentence at the generality printed, with no extension of $\mu$ supplied. The mission's milestone [`Garrido.hasInvariantExtensionProperty_of_isAmenable`](https://prove2.me/theorems/0bf3524a-e23e-4619-abfd-96d6f28107e5) states it for the algebra of all subsets of a $G$-set, with an extension of $\mu$ to all subsets given as a hypothesis; `Garrido.exists_invariant_extension_of_isSetRing` removes that hypothesis for power sets. A general boolean algebra needs, in addition, the recalled extension `Garrido.exists_extension_of_isBooleanSubring` and a $G$-equivariant Stone representation.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, Theorem 2.6; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Garrido_BooleanExtension

namespace Garrido

theorem satisfiesInvariantExtensionTheorem_of_isAmenable {G : Type*} [Group G]
    (hG : IsAmenable G) : SatisfiesInvariantExtensionTheorem G := by
  sorry

end Garrido
