-- Prove2me | Theorems.Thm_OnlineSetCover_Unweighted_lemma_2_1
-- name    : OnlineSetCover.Unweighted.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:05:03.89799+00:00
-- url     : https://prove2.me/theorems/706b88a3-91fb-4961-9ca3-b25d357d0d20
-- title:
--   Lemma 2.1 — at most $|\mathcal C_{OPT}|(\log_2 m+2)$ weight augmentations
-- statement:
--   Consider the unweighted online set-cover algorithm of Section 2 on an instance with $m$ sets. Let $\sigma$ be any sequence of arriving elements and let $\mathcal C_{OPT}$ be any family of sets covering every element of $\sigma$. Then in every run of the algorithm on $\sigma$, the number $a$ of iterations in which a weight augmentation is performed satisfies
--
--   $$a\;\le\;|\mathcal C_{OPT}|\cdot(\log_2 m+2).$$
--
--   This bounds the number of iterations in which the algorithm may add sets to its cover; combined with the per-iteration bound of Lemma 2.2 it bounds the size of the final cover (Theorem 2.3).
--
--   **Formalization Note** The logarithm is base 2: the paper's $\log m+2$ is $\log_2(4m)$, the number of doublings that take a weight from its initial value $1/(2m)$ to at most $2$. The statement holds for every family covering the arrivals, in particular for an optimal one. Runs are those of the relation `Run` of the definition file; arrival lists may repeat elements.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 363, Lemma 2.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Unweighted_Algorithm
open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Unweighted

/-- Lemma 2.1 (Alon et al. 2009, p. 363): for every family `OPT` of sets covering every element
of the arrival list `σ`, every run of the unweighted algorithm on `σ` performs at most
`|OPT| · (log₂ m + 2)` weight augmentations, where `m` is the number of sets. -/
theorem lemma_2_1 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (σ : List E) (OPT : Finset T)
    (hOPT : ∀ j ∈ σ, coveredBy inst OPT j)
    (s : State T) (a : ℕ) (hrun : Run inst σ s a) :
    (a : ℝ) ≤ (OPT.card : ℝ) * (Real.logb 2 (Fintype.card T) + 2) := by sorry

end OnlineSetCover.Unweighted
