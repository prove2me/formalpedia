-- Prove2me | Theorems.Thm_OnlineSetCover_Unweighted_theorem_2_3
-- name    : OnlineSetCover.Unweighted.theorem_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:05:24.705299+00:00
-- url     : https://prove2.me/theorems/0a9d527b-63e1-4e8e-9627-20aa0636a611
-- title:
--   Theorem 2.3 — the unweighted algorithm covers $X'$ with $|\mathcal C|\le\lceil 4\ln n\rceil\,|\mathcal C_{OPT}|(\log_2 m+2)$
-- statement:
--   Let a set-cover instance have a ground set of $n\ge2$ elements and $m$ sets, all of unit cost. Let $\sigma$ be any sequence of elements given by the adversary (the set $X'$ of given elements), and let $\mathcal C_{OPT}$ be any family of sets covering every element of $\sigma$. Then:
--
--   1. the unweighted online algorithm of Section 2 has a run on $\sigma$ (at every arrival an admissible choice exists), and
--   2. every run of the algorithm on $\sigma$ ends with a cover $\mathcal C$ that is a feasible cover of $X'$ (every element of $\sigma$ lies in some member of $\mathcal C$) and satisfies
--
--   $$|\mathcal C|\;\le\;\lceil 4\ln n\rceil\cdot|\mathcal C_{OPT}|\cdot(\log_2 m+2).$$
--
--   In particular the algorithm is $O(\log m\log n)$-competitive for unweighted online set cover: the paper writes $|\mathcal C|=O(|\mathcal C_{OPT}|\log m\log n)$, and its proof yields the explicit bound above (Lemma 2.1 times Lemma 2.2).
--
--   **Formalization Note** The paper writes $O(\cdot)$; the proof yields the constant $\lceil 4\ln n\rceil\cdot(\log_2 m+2)$, where $\lceil 4\ln n\rceil$ is the paper's "$4\log n$" sets per augmentation (natural logarithm, rounded up) and $\log_2 m+2=\log_2(4m)$. The hypothesis $n\ge2$ is the paper's tacit assumption behind $\log n$: for $n=1$ no set may be added and the arriving element stays uncovered. Since the algorithm's choice in step 2(c) is not determined, it is a relation, and part 1 (existence of a run) is part of the statement. Arrival lists may repeat elements.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 364, Theorem 2.3

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Unweighted_Algorithm
open OnlinePrimalDual.OnlineSetCover

namespace OnlineSetCover.Unweighted

/-- Theorem 2.3 (Alon et al. 2009, p. 364), with the explicit constant of its proof. Let the
instance have `n ≥ 2` elements and `m` sets, let `σ` be an arrival list and `OPT` any family of
sets covering every element of `σ`. Then
(a) the unweighted algorithm has a run on `σ` (an admissible choice exists at every step), and
(b) every run ends with a cover `𝒞` that covers every element of `σ` and satisfies
`|𝒞| ≤ ⌈4 ln n⌉ · |OPT| · (log₂ m + 2)`. -/
theorem theorem_2_3 {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (hn : 2 ≤ Fintype.card E)
    (σ : List E) (OPT : Finset T) (hOPT : ∀ j ∈ σ, coveredBy inst OPT j) :
    (∃ (s : State T) (a : ℕ), Run inst σ s a) ∧
      ∀ (s : State T) (a : ℕ), Run inst σ s a →
        (∀ j ∈ σ, coveredBy inst s.cover j) ∧
          (s.cover.card : ℝ) ≤
            (setCap (Fintype.card E) : ℝ) * (OPT.card : ℝ) * (Real.logb 2 (Fintype.card T) + 2) := by sorry

end OnlineSetCover.Unweighted
