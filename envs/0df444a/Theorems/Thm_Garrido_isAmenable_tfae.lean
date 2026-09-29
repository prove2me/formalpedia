-- Prove2me | Theorems.Thm_Garrido_isAmenable_tfae
-- name    : Garrido.isAmenable_tfae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:11:33.271855+00:00
-- url     : https://prove2.me/theorems/7cb5f344-1e1e-4a98-a570-2db7094089e5
-- title:
--   Theorem 1.15 — amenable, invariant mean, and not paradoxical are equivalent
-- statement:
--   For a group $G$ the following three are equivalent:
--
--   1. $G$ is amenable — there is a finitely additive left-invariant probability measure on
--      $\mathcal{P}(G)$;
--   2. there is a left-invariant mean on $G$ — a positive, normalised, left-invariant linear
--      functional on $\ell^\infty(G)$;
--   3. $G$ is not paradoxical, i.e. $G$, acting on itself by left translation, is not
--      $G$-paradoxical.
--
--   Clause 3 is the non-paradoxicality of the whole group, which is the case $E = G$ of the
--   relativised definition of paradoxicality. Clause 2 quantifies existentially over linear
--   functionals on $\ell^\infty(G)$, realised as the $p = \infty$ Lebesgue space of $G$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 5, Theorem 1.15; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. The equivalence of the measure and mean formulations is due to M. M. Day, "Amenable semigroups", Illinois J. Math. 1 (1957), 509–544, as the source's historical note records; https://doi.org/10.1215/ijm/1255380675

import Mathlib
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability

namespace Garrido

theorem isAmenable_tfae (G : Type*) [Group G] :
    [IsAmenable G,
      HasInvariantMean G,
      ¬ IsParadoxical G (Set.univ : Set G)].TFAE := by
  sorry

end Garrido
