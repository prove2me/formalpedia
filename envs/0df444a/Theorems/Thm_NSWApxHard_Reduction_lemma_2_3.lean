-- Prove2me | Theorems.Thm_NSWApxHard_Reduction_lemma_2_3
-- name    : NSWApxHard.Reduction.lemma_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:20.98299+00:00
-- url     : https://prove2.me/theorems/dc4ebf7e-d997-489d-ac83-896b890888ca
-- title:
--   Lemma 2.3 — for α ∈ (1/3, 1/2) some optimal allocation gives each vertex agent ≤ 1 vertex item and obeys the four-step rule
-- statement:
--   Let $G$ be a 3-regular graph on $N$ vertices, let $\alpha\in(1/3,1/2)$, and consider the reduced instance with $k<N$ vertex items. Then there is an allocation $x$ of maximum Nash social welfare in which every vertex agent holds at most one vertex item and every shared item $i(v,e)$ satisfies the following rule:
--   1. if $a(v)$ has 1 vertex item, $a(e)$ gets $i(v,e)$;
--   2. else, if $a(e)$ has 1 shared item other than $i(v,e)$, $a(v)$ gets $i(v,e)$;
--   3. else, if $a(v)$ has 2 shared items other than $i(v,e)$, $a(e)$ gets $i(v,e)$;
--   4. else $a(v)$ gets $i(v,e)$.
--
--   The rule pins down the structure of an optimal allocation completely enough to count the agents of each utility level, which is what Lemma 2.4 does.
--
--   Differences from the source:
--   - generalization: c_min N vertex items with c_min N < N → any number k < N of vertex items; reason: the proof uses Lemma 2.2, which needs only fewer vertex items than vertex agents, and k = c_min N is the page's case.
--   - reading: "a(e) has 1 shared item other than i(v, e)", "a(v) has 2 shared items other than i(v, e)" → the number of all shared items other than i(v, e) held by the agent is 1, resp. 2; reason: literal reading; in an optimal allocation no agent holds a shared item worth 0 to it, so the count equals the count of the agent's own shared items.
--   - reading: the section's standing assumption that G is 3-regular (p. 2) → an explicit hypothesis; reason: Lemma 2.3's sentence does not repeat it.
-- source:
--   Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, arXiv:1507.01159v1, p. 3, Lemma 2.3 (proof pp. 3–4)

import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Lemma 2.3 (Lee, p. 3): for `α ∈ (1/3, 1/2)` and `k < N`, some optimal allocation of the
reduced instance gives each vertex agent at most one vertex item, and every shared item
`i(v, e)` is allocated by the four-step rule `Rule`. -/
theorem lemma_2_3 {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (hk : k < N) :
    ∃ x : Item G k → Agent G, IsOptimal (redUtil G k α) x ∧ (∀ v : Fin N, vItems x v ≤ 1) ∧
      ∀ s : Inc G, Rule x s := by sorry

end NSWApxHard.Reduction
