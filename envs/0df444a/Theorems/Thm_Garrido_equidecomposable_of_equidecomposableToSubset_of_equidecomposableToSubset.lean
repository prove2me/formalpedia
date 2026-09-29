-- Prove2me | Theorems.Thm_Garrido_equidecomposable_of_equidecomposableToSubset_of_equidecomposableToSubset
-- name    : Garrido.equidecomposable_of_equidecomposableToSubset_of_equidecomposableToSubset
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:09:12.27323+00:00
-- url     : https://prove2.me/theorems/8e68fddd-e168-402a-b25d-ad08e241eecb
-- title:
--   Theorem 1.2 — Banach–Schröder–Bernstein
-- statement:
--   Let a group $G$ act on a set $X$ and let $A, B \subseteq X$. If
--   $A \lesssim B$ and $B \lesssim A$ then $A \sim B$.
--
--   Here $A \lesssim B$ means $A$ is $G$-equidecomposable with some subset of $B$, and $A \sim B$
--   means $A$ and $B$ are $G$-equidecomposable. This is the Schröder–Bernstein phenomenon for
--   equidecomposability: two-sided domination gives equidecomposability itself, with the pieces
--   still finite in number.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 2, Theorem 1.2 (Banach–Schröder–Bernstein); https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. Mathlib records the same statement as an open TODO in Mathlib/Algebra/Group/Action/Equidecomp.lean. The result is classical, going back to S. Banach and A. Tarski, "Sur la décomposition des ensembles de points en parties respectivement congruentes", Fund. Math. 6 (1924), 244–277; https://doi.org/10.4064/fm-6-1-244-277

import Mathlib
import Definitions.Def_Garrido_Equidecomposability

namespace Garrido

theorem equidecomposable_of_equidecomposableToSubset_of_equidecomposableToSubset
    {G X : Type*} [Group G] [MulAction G X] (A B : Set X)
    (hAB : EquidecomposableToSubset G A B) (hBA : EquidecomposableToSubset G B A) :
    Equidecomposable G A B := by
  sorry

end Garrido
