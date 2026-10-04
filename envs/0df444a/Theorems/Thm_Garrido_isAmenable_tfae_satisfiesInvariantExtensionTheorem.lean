-- Prove2me | Theorems.Thm_Garrido_isAmenable_tfae_satisfiesInvariantExtensionTheorem
-- name    : Garrido.isAmenable_tfae_satisfiesInvariantExtensionTheorem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T22:40:25.518479+00:00
-- url     : https://prove2.me/theorems/068e952b-c377-4dce-a540-c47dde437fcc
-- title:
--   Garrido, Theorem 2.7 — amenability, an invariant mean, non-paradoxicality and the Invariant Extension Theorem are equivalent
-- statement:
--   For a group $G$ the following are equivalent: $G$ is amenable (`IsAmenable G`); there is a left-invariant mean on $G$ (`HasInvariantMean G`); $G$ is not paradoxical under left multiplication (`¬ IsParadoxical G Set.univ`); $G$ satisfies the Invariant Extension Theorem for every boolean algebra (`SatisfiesInvariantExtensionTheorem G`).
--
--   Garrido writes on p. 7: “**Theorem 2.7.** *For a group $G$, the following are equivalent: 1. $G$ is amenable, that is, there is a finitely additive left-invariant probability measure on $\mathcal B(G)$; 2. there is a left-invariant mean on $G$; 3. $G$ is not paradoxical; 4. $G$ satisfies the Invariant Extension Theorem.*” Item 4 is read at the generality of Theorem 2.6 (any boolean algebra, any subring, no extension supplied). The mission's milestone [`Garrido.isAmenable_tfae_four`](https://prove2.me/theorems/688f9c00-7c33-489b-8ad9-1ef7e6079b1e) is the same equivalence with item 4 restricted to the algebras of all subsets of $G$-sets and an extension supplied. `IsAmenable`, `HasInvariantMean` and `IsParadoxical` are from the Garrido amenability and equidecomposability definitions.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, Theorem 2.7; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Garrido_BooleanExtension

namespace Garrido

theorem isAmenable_tfae_satisfiesInvariantExtensionTheorem (G : Type*) [Group G] :
    [IsAmenable G,
      HasInvariantMean G,
      ¬ IsParadoxical G (Set.univ : Set G),
      SatisfiesInvariantExtensionTheorem G].TFAE := by
  sorry

end Garrido
