-- Prove2me | Theorems.Thm_Garrido_isAmenable_and_not_elementaryAmenable_grigorchukGroup
-- name    : Garrido.isAmenable_and_not_elementaryAmenable_grigorchukGroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T13:13:19.510424+00:00
-- url     : https://prove2.me/theorems/b2b1f5fb-0a0f-45eb-ba44-b58b8678d642
-- title:
--   Theorem 4.1 — the Grigorchuk group is amenable but not elementary amenable
-- statement:
--   The (first) Grigorchuk group is amenable but not elementary amenable:
--
--   $$\Gamma \in AG \setminus EG.$$
--
--   It answers the elementary-amenable half of the von Neumann–Day problem: $EG \ne AG$.
--
--   **Formalization Note.** Amenability is the published `IsAmenable` (a finitely additive,
--   left-invariant measure on all subsets of $\Gamma$ with total mass $1$) and elementary
--   amenability the published `Chou.ElementaryAmenable`.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 12, Theorem 4.1; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. The result is due to R. I. Grigorchuk, "Degrees of growth of finitely generated groups, and the theory of invariant means", Math. USSR-Izvestiya 25 (1985), 259; https://doi.org/10.1070/IM1985v025n02ABEH001281

import Mathlib
import Definitions.Def_Garrido_Grigorchuk
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_ElementaryAmenable

namespace Garrido

theorem isAmenable_and_not_elementaryAmenable_grigorchukGroup :
    IsAmenable GrigorchukGroup ∧ ¬ Chou.ElementaryAmenable GrigorchukGroup := by
  sorry

end Garrido
