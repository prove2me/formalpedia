-- Prove2me | Theorems.Thm_OnlineSetCover_Unweighted_lemma_2_2
-- name    : OnlineSetCover.Unweighted.lemma_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:05:22.14584+00:00
-- url     : https://prove2.me/theorems/73f0bae0-9045-4285-9888-66b54f8edc9f
-- title:
--   Lemma 2.2 — at most $\lceil 4\ln n\rceil$ sets suffice to keep $\Phi$ from increasing
-- statement:
--   Consider an iteration of the unweighted online set-cover algorithm in which a weight augmentation is performed. Let the instance have $n$ elements, let the current set weights $w_S$ be positive, let $\mathcal C$ be the current cover, and let $j$ be the arriving element, with $w_j=\sum_{S\in\mathcal S_j}w_S<1$. Let $k$ be the minimal integer with $2^k w_j>1$, and let $w'$ be the weights after multiplying $w_S$ by $2^k$ for every $S\in\mathcal S_j$. Then there is a family $F\subseteq\mathcal S_j$ with $|F|\le\lceil 4\ln n\rceil$ such that
--
--   $$\Phi(w',\mathcal C\cup F)\;\le\;\Phi(w,\mathcal C),\qquad \Phi(w,\mathcal C)=\sum_{j'\notin C}n^{2w_{j'}}.$$
--
--   That is, the algorithm can always complete step 2(c): the potential after the iteration $\Phi_e$ is at most the potential before it $\Phi_s$. This is what makes the algorithm well defined and keeps the potential nonincreasing throughout the run.
--
--   **Formalization Note** The paper's "at most $4\log n$ sets" is read as $\lceil 4\ln n\rceil$ with the natural logarithm: the proof repeats a random choice $4\log n$ times and uses $(1-\delta/2)^{4\log n}\le n^{-2\delta}$, which needs the natural logarithm and a number of repetitions at least $4\ln n$. The lemma is stated for any state with positive weights (the algorithm maintains $w_S>0$), not only for reachable ones.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 364, Lemma 2.2

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlineSetCover_Unweighted_Algorithm
open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Unweighted

/-- Lemma 2.2 (Alon et al. 2009, p. 364): in an iteration with a weight augmentation (the
arriving element `j` has `w_j < 1`, `k` is the minimal integer with `2^k w_j > 1`, and every set
containing `j` has its weight multiplied by `2^k`), there is a family `F` of at most `⌈4 ln n⌉`
sets containing `j` such that the potential after the iteration, with cover `𝒞 ∪ F` and the
augmented weights, is at most the potential before it. Weights are positive, as the algorithm
maintains. -/
theorem lemma_2_2 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (hw : ∀ S, 0 < w S)
    (cover : Finset T) (j : E) (k : ℕ)
    (hlt : elementWeight inst w j < 1)
    (hk : IsAugExponent (elementWeight inst w j) k) :
    ∃ F : Finset T, F ⊆ inst.elemSets j ∧ F.card ≤ setCap (Fintype.card E) ∧
      potential inst (augment inst w j k) (cover ∪ F) ≤ potential inst w cover := by sorry

end OnlineSetCover.Unweighted
