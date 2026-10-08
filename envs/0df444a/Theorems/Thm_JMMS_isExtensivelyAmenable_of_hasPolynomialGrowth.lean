-- Prove2me | Theorems.Thm_JMMS_isExtensivelyAmenable_of_hasPolynomialGrowth
-- name    : JMMS.isExtensivelyAmenable_of_hasPolynomialGrowth
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-07T09:31:39.140994+00:00
-- url     : https://prove2.me/theorems/b7c17a24-3ff7-451c-8a2b-7eb8dd8c318c
-- title:
--   Question 1.11 — a transitive action with polynomially growing Schreier graph is extensively amenable (open)
-- statement:
--   Let a group $G$ act transitively on a set $X$, let $S$ be a finite symmetric subset of $G$ that generates $G$, and let $x_0 \in X$. If the orbital Schreier graph $\Gamma(G, X, S)$ grows polynomially — there are $C$ and $d$ such that for every $n$ the ball of radius $n$ about $x_0$, the set of points $s_k \cdots s_1 x_0$ with $k \le n$ and every $s_i \in S$, is finite with at most $C(n+1)^d$ elements — then the action is extensively amenable.
--
--   Juschenko, Matte Bon, Monod and de la Salle, p. 6: “Question 1.11. Assume that $\Gamma(G, X, S)$ grows polynomially. Does this imply that $G \curvearrowright X$ is extensively amenable?” The setting is on p. 5: “there is no loss of generality in assuming that $G$ is finitely generated and acts transitively on $X$ (Lemma 2.2). Assuming this, let $S$ be a finite symmetric generating set of $G$.”
--
--   The question is open; the statement asserts the positive answer, and a disproof is as welcome as a proof.
-- source:
--   Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 6, Question 1.11 (open)

import Mathlib
import Definitions.Def_IntervalExchange

open IntervalExchange

namespace JMMS

theorem isExtensivelyAmenable_of_hasPolynomialGrowth {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (S : Finset G) (hsymm : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (x₀ : X)
    (hpoly : HasPolynomialGrowth (S : Set G) x₀) : IsExtensivelyAmenable G X := by
  sorry

end JMMS
