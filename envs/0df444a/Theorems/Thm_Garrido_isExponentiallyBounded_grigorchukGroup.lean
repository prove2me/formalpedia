-- Prove2me | Theorems.Thm_Garrido_isExponentiallyBounded_grigorchukGroup
-- name    : Garrido.isExponentiallyBounded_grigorchukGroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T13:12:55.195752+00:00
-- url     : https://prove2.me/theorems/b360550b-d422-465a-baf6-eac061a7c9fe
-- title:
--   Theorem 4.9 — Γ has subexponential growth
-- statement:
--   The Grigorchuk group has subexponential growth: for its finite generating set, the ball of
--   radius $k$ eventually has at most $c^k$ elements for every $c > 1$.
--
--   $$\lim_{k \to \infty} |B_S(k)|^{1/k} = 1.$$
--
--   **Formalization Note.** Subexponential growth is the published `Chou.IsExponentiallyBounded`:
--   there is a finite generating set whose balls eventually have at most $c^k$ elements for every
--   $c > 1$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 16, Theorem 4.9; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. The result is due to R. I. Grigorchuk, "Degrees of growth of finitely generated groups, and the theory of invariant means", Math. USSR-Izvestiya 25 (1985), 259; https://doi.org/10.1070/IM1985v025n02ABEH001281

import Mathlib
import Definitions.Def_Garrido_Grigorchuk
import Definitions.Def_Chou_Growth

namespace Garrido

theorem isExponentiallyBounded_grigorchukGroup : Chou.IsExponentiallyBounded GrigorchukGroup := by
  sorry

end Garrido
