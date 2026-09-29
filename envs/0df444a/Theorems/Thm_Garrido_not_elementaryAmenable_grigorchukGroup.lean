-- Prove2me | Theorems.Thm_Garrido_not_elementaryAmenable_grigorchukGroup
-- name    : Garrido.not_elementaryAmenable_grigorchukGroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T13:11:00.513849+00:00
-- url     : https://prove2.me/theorems/16ad039d-b752-4ae7-9268-f497ecfe189c
-- title:
--   p. 14 — Γ is not elementary amenable
-- statement:
--   The Grigorchuk group is not elementary amenable:
--
--   $$\Gamma \notin EG.$$
--
--   **Formalization Note.** Elementary amenability is the published `Chou.ElementaryAmenable`, the
--   smallest class containing the finite and the abelian groups and closed under isomorphism,
--   subgroups, quotients, extensions and directed unions.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 14, the sentence after Proposition 4.7; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Grigorchuk
import Definitions.Def_Chou_ElementaryAmenable

namespace Garrido

theorem not_elementaryAmenable_grigorchukGroup : ¬ Chou.ElementaryAmenable GrigorchukGroup := by
  sorry

end Garrido
