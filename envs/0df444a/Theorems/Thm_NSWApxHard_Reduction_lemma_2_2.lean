-- Prove2me | Theorems.Thm_NSWApxHard_Reduction_lemma_2_2
-- name    : NSWApxHard.Reduction.lemma_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:37.713211+00:00
-- url     : https://prove2.me/theorems/10a74969-8aa7-4826-807c-6c81e797646d
-- title:
--   Lemma 2.2 — some optimal allocation gives each vertex agent at most one vertex item
-- statement:
--   Let $G$ be a 3-regular graph on $N$ vertices, let $\alpha\in(1/3,1/2)$, and consider the reduced instance with $k<N$ vertex items (fewer vertex items than vertex agents). Then there is an allocation $x$ of maximum Nash social welfare such that
--   $$\mathrm{vItems}_x(v)\le 1\qquad\text{for every vertex } v,$$
--   i.e. every vertex agent holds at most one vertex item.
--
--   This is the first normal form of an optimal allocation used in the soundness analysis.
--
--   Differences from the source:
--   - generalization: c_min N vertex items with c_min N < N → any number k < N of vertex items; reason: the proof uses only that there are fewer vertex items than vertex agents (p. 3), and k = c_min N is the page's case.
--   - reading: the section's standing assumptions (G 3-regular, "Let α be a constant in (1/3, 1/2)", p. 2) → explicit hypotheses; reason: Lemma 2.2's sentence does not repeat them.
-- source:
--   Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, arXiv:1507.01159v1, p. 2, Lemma 2.2 (proof p. 3)

import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Lemma 2.2 (Lee, p. 2): if there are fewer vertex items than vertex agents (`k < N`), some
optimal allocation of the reduced instance gives each vertex agent at most one vertex item. -/
theorem lemma_2_2 {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (hk : k < N) :
    ∃ x : Item G k → Agent G,
      IsOptimal (redUtil G k α) x ∧ ∀ v : Fin N, vItems x v ≤ 1 := by sorry

end NSWApxHard.Reduction
