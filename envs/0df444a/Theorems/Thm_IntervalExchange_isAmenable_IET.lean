-- Prove2me | Theorems.Thm_IntervalExchange_isAmenable_IET
-- name    : IntervalExchange.isAmenable_IET
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-07T09:33:44.252414+00:00
-- url     : https://prove2.me/theorems/5ea5e407-d4c1-4a96-8927-2d27a980b215
-- title:
--   Question 1.6 — the group IET of interval exchange transformations is amenable
-- statement:
--   The group $\mathrm{IET}$ of interval exchange transformations of $\mathbf R/\mathbf Z$ is amenable: it carries a finitely additive, left-invariant probability measure defined on all of its subsets.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 4: “A related open question raised in [dC13, p.4] is as follows. Question 1.6. Is the group IET amenable?” de Cornulier, p. 1064-04: “La question de la moyennabilité du groupe entier IET est ouverte.”
--
--   The question is open; this statement asserts the positive answer, and a disproof settles the question the other way.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 4, Question 1.6 (open), attributed to de Cornulier, Y., Groupes pleins-topologiques [d'après Matui, Juschenko, Monod, ...], Séminaire Bourbaki, exposé 1064, Astérisque 361 (2014) 183–223 (arXiv:2002.09342), p. 1064-04

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace IntervalExchange

theorem isAmenable_IET : Garrido.IsAmenable ↥IET := by
  sorry

end IntervalExchange
