-- Prove2me | Theorems.Thm_Garrido_isAmenable_tfae_four
-- name    : Garrido.isAmenable_tfae_four
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:35:33.309513+00:00
-- url     : https://prove2.me/theorems/688f9c00-7c33-489b-8ad9-1ef7e6079b1e
-- title:
--   Theorem 2.7 — amenability, an invariant mean, non-paradoxicality and the invariant extension property are equivalent
-- statement:
--   For a group $G$ the following four are equivalent:
--
--   1. $G$ is amenable — there is a finitely additive left-invariant probability measure on
--      $\mathcal{P}(G)$;
--   2. there is a left-invariant mean on $\ell^\infty(G)$;
--   3. $G$ is not paradoxical;
--   4. $G$ has the invariant extension property.
--
--   This is the source's running list of equivalent definitions extended by the fourth clause; the
--   first three are the same as in Theorem 1.15, which the source states separately.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, Theorem 2.7; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability

namespace Garrido

theorem isAmenable_tfae_four (G : Type*) [Group G] :
    [IsAmenable G,
      HasInvariantMean G,
      ¬ IsParadoxical G (Set.univ : Set G),
      HasInvariantExtensionProperty G].TFAE := by
  sorry

end Garrido
