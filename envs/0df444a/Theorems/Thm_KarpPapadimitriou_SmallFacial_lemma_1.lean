-- Prove2me | Theorems.Thm_KarpPapadimitriou_SmallFacial_lemma_1
-- name    : KarpPapadimitriou.SmallFacial.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:40:33.427855+00:00
-- url     : https://prove2.me/theorems/abfd9625-8daf-4e23-86f8-41a8c8df3451
-- title:
--   Lemma 1 — zero-one and integer-programming-type problems have small facial descriptions
-- statement:
--   Let $C=(L,n,S)$ be a combinatorial optimization problem whose feasible solutions are nonnegative integer vectors. If every feasible vector is a zero-one vector, or each feasible set is the set of nonnegative integer solutions of an encoded integral system $A(z)x\le b(z)$, then there exists one collection $F$ of integral inequalities describing every rational hull $\mathrm{CH}(S(z))$, with a uniform polynomial bound on every coefficient:
--   $$\exists F\;\bigl[F\text{ is a facial description of }C\ \land\ \exists k\in\mathbb N\;\forall\langle z,f,g\rangle\in F,\ \max_i|f_i|,|g|\le2^{(|z|+n(z))^k+k}\bigr].$$
--   Thus both classes admit a complete linear description whose individual inequalities have polynomial bit length, even when the description has many inequalities.
--
--   **Formalization Note** The paper's $R$ denotes $\mathbb Q$. Its polynomial-time language requirements are unnecessary for this lemma and are absent from the data type, so the statement is stronger than Lemma 1 for c.o.p.s as originally defined. The encoding of an IP-type input requires its total coefficient size to be at most $|z|$. The result covers empty feasible sets, lower-dimensional hulls, dimension zero, and unbounded IP hulls.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 5, Lemma 1; https://dspace.mit.edu/server/api/core/bitstreams/eb122126-c312-4445-a8d2-153e3e7d285f/content

import Mathlib
import Definitions.Def_KarpPapadimitriou_SmallFacial_COP

namespace KarpPapadimitriou.SmallFacial

/-- Lemma 1, p. 5: both named classes have a small facial description. -/
theorem lemma_1 (C : COP) (hC : IsZeroOne C ∨ IsIPType C) :
    ∃ F : Set (Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ),
      IsFacialDescription C F ∧ IsSmall C F := by sorry

end KarpPapadimitriou.SmallFacial
