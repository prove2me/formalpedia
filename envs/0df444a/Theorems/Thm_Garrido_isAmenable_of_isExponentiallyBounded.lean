-- Prove2me | Theorems.Thm_Garrido_isAmenable_of_isExponentiallyBounded
-- name    : Garrido.isAmenable_of_isExponentiallyBounded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:41:35.471663+00:00
-- url     : https://prove2.me/theorems/2d340ef6-532c-49e8-b835-057acb65b0ba
-- title:
--   Theorem 3.8 — a group of subexponential growth is amenable
-- statement:
--   If a group $G$ has subexponential growth then $G$ is amenable.
--
--   Subexponential growth is the published `Chou.IsExponentiallyBounded`: for some finite
--   generating set $S$ of $G$ and every real $c > 1$, the ball $B_S(n)$ of radius $n$ in the word
--   metric satisfies $|B_S(n)| \le c^n$ for all sufficiently large $n$. Because that predicate
--   quantifies over a *finite generating set*, it carries the finite-generation hypothesis that the
--   source's Theorem 3.8 leaves implicit.
--
--   The source's statement says "All subgroups of subexponential growth"; "groups" is meant, as
--   the introduction to Section 3 (p. 8) and the proof both make clear.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 10, Theorem 3.8. The source's statement reads "All subgroups of subexponential growth are amenable", where "groups" is meant: the introduction to Section 3 (p. 8) says "all groups of subexponential growth are (supra)amenable" and the proof begins "Let G have subexponential growth". Finite generation, required for the growth function of Definition 3.7 to be defined, is left implicit in the statement and is supplied here by the imported growth definition; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_Growth

namespace Garrido

theorem isAmenable_of_isExponentiallyBounded (G : Type*) [Group G]
    (hG : Chou.IsExponentiallyBounded G) :
    IsAmenable G := by
  sorry

end Garrido
