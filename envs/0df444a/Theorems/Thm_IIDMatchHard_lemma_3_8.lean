-- Prove2me | Theorems.Thm_IIDMatchHard_lemma_3_8
-- name    : IIDMatchHard.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:28.471216+00:00
-- url     : https://prove2.me/theorems/a2635171-ab5a-4552-82f5-27c64a7d2351
-- title:
--   Lemma 3.8 — max cuts of random subgraphs of blow-ups
-- statement:
--   Let $G$ be a finite simple graph with $m$ edges, let $B\ge1$, and let $\tilde G$ be its blow-up. If a random set $A$ contains every vertex of $\tilde G$ independently with probability $p\in[0,1]$, then
--   $$p^2C(\tilde G)\ \le\ \mathbb E\big[C(\tilde G[A])\big]\ \le\ p^2C(\tilde G)+mB^{3/2},$$
--   where $\tilde G[A]$ is the subgraph of $\tilde G$ induced by $A$.
--
--   The maximum cut of a random induced subgraph of a blow-up is close to what a fixed maximum cut of $\tilde G$ achieves on it. This bounds the gain from adaptivity in Lemma 3.9.
--
--   Differences from the source:
--   - encoding: the expectation over the random set A → the finite sum Σ_A p^{|A|}(1 − p)^{nB − |A|} C(G̃[A]); reason: the law of A; same value
--   - encoding: a probability p; B^{3/2} → p ∈ [0, 1] stated as hypotheses; the real power (B : ℝ)^(3/2); reason: Lean convention; same quantities
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Lemma 3.8, p.10 (PDF p.11); proof in App. B.7, pp.20–21

import Definitions.Def_IIDMatchHard_Cut

set_option autoImplicit false

namespace IIDMatchHard

/-- **Lemma 3.8 (Random subgraphs of blow-ups).** If a random set `A` contains every vertex of
`G̃` independently with probability `p`, then `p²C(G̃) ≤ E[C(G̃[A])] ≤ p²C(G̃) + mB^{3/2}`.
Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Lemma 3.8, p.10 (PDF p.11); proof in App. B.7, pp.20–21.

**Formalization Note.** `G̃ = blowUp G B` with `B ≥ 1`, `m` is the number of edges of `G` (not
of `G̃`), `p ∈ [0, 1]`, `G̃[A]` is the induced subgraph on `A`, and `B^{3/2}` is the real power. -/
theorem lemma_3_8 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (B : ℕ)
    (hB : 1 ≤ B) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ^ 2 * (maxCut (blowUp G B) : ℝ) ≤
        randSubsetExp p (fun A : Finset (V × Fin B) =>
          (maxCut ((blowUp G B).induce (A : Set (V × Fin B))) : ℝ)) ∧
      randSubsetExp p (fun A : Finset (V × Fin B) =>
          (maxCut ((blowUp G B).induce (A : Set (V × Fin B))) : ℝ)) ≤
        p ^ 2 * (maxCut (blowUp G B) : ℝ) + (numEdges G : ℝ) * (B : ℝ) ^ (3 / 2 : ℝ) := by sorry

end IIDMatchHard
