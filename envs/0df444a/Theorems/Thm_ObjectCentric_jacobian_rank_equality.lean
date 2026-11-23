-- Prove2me | Theorems.Thm_ObjectCentric_jacobian_rank_equality
-- name    : ObjectCentric.jacobian_rank_equality
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:38:37.057294+00:00
-- url     : https://prove2.me/theorems/9cdf3f98-d4a3-42ab-b708-db1bfa1a3ad0
-- title:
--   Lemma 4: ground-truth and inferred sub-mechanisms have equal rank
-- statement:
--   Let $M\ge1$, $\mathcal Z=(\mathbb R^M)^K$ and $\mathcal X\subseteq\mathbb R^N$. Let $\mathbf f,\hat{\mathbf f}:\mathcal Z\to\mathcal X$ be diffeomorphisms with inverses $\mathbf g,\hat{\mathbf g}:\mathcal X\to\mathcal Z$. Then for all $\mathbf z\in\mathcal Z$ and all nonempty $S\subseteq[N]$,
--
--   $$\operatorname{rank}\mathbf J\mathbf f_S(\mathbf z)=\operatorname{rank}\mathbf J\hat{\mathbf f}_S(\hat{\mathbf z}),\qquad\hat{\mathbf z}:=\hat{\mathbf g}(\mathbf f(\mathbf z)).$$
--
--   **Formalization Note** The slot dimension is assumed to satisfy $M\ge1$, which the paper takes for granted (each slot encodes $M$ object properties). This statement does not need it: for $M=0$ every rank in it is $0$ and it still holds.
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1 (2023), Appendix A, Lemma 4, p. 16

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

theorem jacobian_rank_equality {K M N : ℕ} (hM : 0 < M) (X : Set (Obs N))
    (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (fhat : Lat K M → Obs N) (ghat : Obs N → Lat K M) (hhat : IsDiffeoWithInv fhat ghat X) :
    ∀ (z : Lat K M) (S : Set (Fin N)), S.Nonempty →
      subRank f z S = subRank fhat (ghat (f z)) S := by sorry

end ObjectCentric
