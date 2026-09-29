-- Prove2me | Theorems.Thm_Garrido_exists_invariant_measure_eq_one_iff_not_isParadoxical
-- name    : Garrido.exists_invariant_measure_eq_one_iff_not_isParadoxical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:09:51.55499+00:00
-- url     : https://prove2.me/theorems/2b8edd96-533b-456a-849b-b2ec32fa06e2
-- title:
--   Theorem 1.11 — Tarski's theorem
-- statement:
--   Let a group $G$ act on a set $X$ and let $E \subseteq X$. Then the following
--   are equivalent:
--
--   - there is a finitely additive $G$-invariant $m : \mathcal{P}(X) \to [0,\infty]$ with
--     $m(E) = 1$;
--   - $E$ is not $G$-paradoxical.
--
--   "Finitely additive" is the mission's finitely additive measure — $m(\emptyset) = 0$ and
--   additivity on disjoint pairs — and "$G$-invariant" is $m(gs) = m(s)$ for
--   every $g \in G$ and every $s \subseteq X$. Note that $m$ is *not* required to be a probability
--   measure on $X$: only $m(E) = 1$ is imposed, and $m$ may take the value $\infty$, matching the
--   source's codomain $[0,\infty]$.
--
--   **$E$ is assumed nonempty, and the biconditional is false without it.** The source states
--   Theorem 1.11 for an arbitrary $E \subseteq X$, but at $E = \emptyset$ the right-hand side holds —
--   the empty set is not paradoxical, since it has no proper subsets — while the left-hand side is
--   unsatisfiable: a finitely additive measure has $m(\emptyset) = 0$, never $1$. The hypothesis is therefore
--   part of the intended statement rather than an addition to it, and Wagon's Corollary 9.2, which
--   the source cites in place of a proof, carries it.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 3, Theorem 1.11 (Tarski); https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. The source states this without proof, citing S. Wagon, The Banach–Tarski Paradox, Cambridge University Press (1985), Corollary 9.2; https://doi.org/10.1017/CBO9780511609596

import Mathlib
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Amenability
open scoped ENNReal

namespace Garrido

theorem exists_invariant_measure_eq_one_iff_not_isParadoxical
    {G X : Type*} [Group G] [MulAction G X] (E : Set X) (hE : E.Nonempty) :
    (∃ m : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m E = 1 ∧
        IsInvariant G m) ↔ ¬ IsParadoxical G E := by
  sorry

end Garrido
