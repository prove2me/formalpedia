-- Prove2me | Theorems.Thm_NSWApxHard_Reduction_optimal_observation
-- name    : NSWApxHard.Reduction.optimal_observation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:38.752996+00:00
-- url     : https://prove2.me/theorems/1f2c37d7-5550-41a2-bf72-e92e8b3df74d
-- title:
--   Soundness observation, p. 2 — in any optimal allocation vertex items go to vertex agents and i(e) goes to a(e)
-- statement:
--   Let $G$ be a 3-regular graph on $N$ vertices, let $\alpha\in(1/3,1/2)$, and consider the reduced instance with $k$ vertex items. In every allocation $x$ of maximum Nash social welfare,
--   1. each vertex item is assigned to some vertex agent $a(v)$, and
--   2. each edge item $i(e)$ is assigned to the corresponding edge agent $a(e)$.
--
--   This normal form is the first step of the soundness analysis; Lemmas 2.2–2.4 build on it.
--
--   Differences from the source:
--   - generalization: c_min N vertex items → any number k of vertex items; reason: the observation does not depend on the number of vertex items, and k = c_min N is the page's case.
--   - reading: the section's standing assumptions (G 3-regular, "Let α be a constant in (1/3, 1/2)", p. 2) → explicit hypotheses; reason: the sentence relies on them without repeating them.
--   - encoding: a 3-regular graph with N vertices → a graph on Fin N, N = 0 allowed; reason: for N = 0 there are no items and the claim is empty, so no instance of the page changes.
-- source:
--   Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, arXiv:1507.01159v1, p. 2, §2, Soundness (first observation)

import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

namespace NSWApxHard.Reduction

/-- Observation (Lee, p. 2): in any optimal allocation of the reduced instance, each vertex item
is assigned to some vertex agent, and each edge item `i(e)` to the edge agent `a(e)`. -/
theorem optimal_observation {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ)
    (α : ℝ) (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (x : Item G k → Agent G) (hx : IsOptimal (redUtil G k α) x) :
    (∀ j : Fin k, ∃ v : Fin N, x (Sum.inl j) = Sum.inl v) ∧
      ∀ e : Edge G, x (Sum.inr (Sum.inl e)) = Sum.inr e := by sorry

end NSWApxHard.Reduction
