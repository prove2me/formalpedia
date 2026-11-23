-- Prove2me | Theorems.Thm_ObjectCentric_mechanism_rank_eq_slot_dim
-- name    : ObjectCentric.mechanism_rank_eq_slot_dim
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:37:50.219273+00:00
-- url     : https://prove2.me/theorems/1a063322-9c83-4b96-b727-2602ed781857
-- title:
--   Lemma 3: every mechanism has rank $M$
-- statement:
--   Let $K\ge0$ and $M\ge1$, let $\mathcal Z=(\mathbb R^M)^K$ and let $\mathcal X\subseteq\mathbb R^N$. Let $\mathbf f:\mathcal Z\to\mathcal X$ be a diffeomorphism with inverse $\mathbf g$ that is compositional. Then every mechanism has rank equal to the slot dimension: for all $\mathbf z\in\mathcal Z$ and $k\in[K]$,
--
--   $$\operatorname{rank}\mathbf J\mathbf f_{I_k}(\mathbf z)=M.$$
--
--   **Formalization Note** The slot dimension is assumed to satisfy $M\ge1$, which the paper takes for granted (each slot encodes $M$ object properties). This statement does not need it: for $M=0$ every rank in it is $0$ and it still holds.
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1 (2023), Appendix A, Lemma 3, p. 15

import Mathlib
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory

namespace ObjectCentric

theorem mechanism_rank_eq_slot_dim {K M N : ℕ} (hM : 0 < M)
    (X : Set (Obs N)) (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) :
    ∀ (z : Lat K M) (k : Fin K), subRank f z (indexSet f z k) = M := by sorry

end ObjectCentric
