-- Prove2me | Theorems.Thm_OnlineCRS_Matroid_chain_validity
-- name    : OnlineCRS.Matroid.chain_validity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:23:56.865179+00:00
-- url     : https://prove2.me/theorems/e819de71-5672-48cb-9681-69f5c5332118
-- title:
--   §2.1, p. 10 — the chain family is a greedy family
-- statement:
--   Let $M$ be a matroid on $N$ and let $N=N_0\supsetneq N_1\supsetneq\cdots\supsetneq N_\ell=\varnothing$ be a strictly descending chain. Define $\mathcal F_x$ by requiring each layer $I\cap(N_i\setminus N_{i+1})$ to be independent in $(M/N_{i+1})|N_i$. Then
--   $$\varnothing\in\mathcal F_x,\qquad J\subseteq I\in\mathcal F_x\Longrightarrow J\in\mathcal F_x,\qquad I\in\mathcal F_x\Longrightarrow I\text{ is independent in }M.$$
--
--   This establishes that the chain construction can serve as the feasible family of a greedy OCRS. The paper cites Soto's matroid result for the final implication.
-- source:
--   arXiv:1508.00142v2, §2.1, p. 10, paragraph after the chain display

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Matroid_Construction

namespace OnlineCRS.Matroid

/-- arXiv:1508.00142v2, §2.1, p. 10, paragraph following the chain display. -/
theorem chain_validity {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) (Nch : ℕ → Finset α) (ℓ : ℕ)
    (hstart : Nch 0 = Finset.univ)
    (hstrict : ∀ i < ℓ, Nch (i + 1) ⊂ Nch i)
    (hend : Nch ℓ = ∅) :
    IsGreedyFamily (fun I : Finset α => M.Indep (I : Set α)) (chainFamily M Nch ℓ) := by sorry

end OnlineCRS.Matroid
