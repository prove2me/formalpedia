-- Prove2me | Theorems.Thm_OnlinePrimalDual_GroupSteiner_lemma11_1_v2
-- name    : OnlinePrimalDual.GroupSteiner.lemma11_1_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:48.043958+00:00
-- url     : https://prove2.me/theorems/5167485f-32a9-4203-b40f-0a9b6f2e5143
-- title:
--   Lemma 11.1 — at the end of every iteration of the online rounding, $\Pr[e \in C] = w_e$ when $w_e \le 1$ and $e\in C$ surely when $w_e > 1$
-- statement:
--   Let $T$ be a rooted tree given by its edge set $E$ and the parent map $e \mapsto e(p)$ (the adjacent edge closer to the root; none for root-incident edges), and let `ord` be a topological order of the edges from the root (a permutation of $E$ in which every edge comes after its parent edge). Let $\delta_1, \delta_2, \dots$ be the non-negative weight increments of the successive iterations of the online fractional algorithm, so that after the iterations processed so far the fractional solution is $w_e = \sum_t (\delta_t)_e$, and assume that every intermediate fractional solution is a flow from the root: $w_e \le w_{e(p)}$ along every root path (`hflow`, for every prefix of the increment sequence). Let $C$ be the random cover produced by the online rounding algorithm of Section 11.2 (`roundCover tr ord δs`): starting from $C=\emptyset$, in each iteration augmenting $w$ to $w' = w+\delta$ the edges with $\delta_e > 0$ are processed in the order `ord`, and $e$ is added to $C$ deterministically if $w'_e > 1$; with probability $\delta_e/(1-w_e)$ if $e$ is root-incident or $w'_{e(p)} > 1$; and otherwise, provided $e(p) \in C$, with probability $\delta_e/(w'_{e(p)} - w_e)$. Then, at the end of the last iteration (hence, applying the statement to every prefix, at the end of every iteration): for every edge $e$ with $w_e \le 1$, $\Pr[e\in C] = w_e$; and for every edge $e$ with $w_e > 1$, $\Pr[e \in C] = 1$.
--
--   **Formalization Note.** The retired version replaced the algorithm's random cover by an arbitrary distribution $\rho$ pinned by four axioms that did not determine its marginals (nothing encoded that an edge is only ever added after its parent, and the third axiom constrained an end-of-iteration conditional probability rather than the coin), so a product distribution refuted it. The new statement defines the cover distribution (`roundCover`) by executing the rounding box literally over the whole sequence of iterations from the empty cover, so the lemma's induction hypothesis is no longer an axiom but the algorithm's history, and states the lemma's two clauses about that distribution with the post-iteration weight (clause (b) with $w_e > 1$ for the current weight, which implies the retired version's reading with the previous weight). Conventions made explicit: increments non-negative (the fractional solution is monotone over time); every intermediate fractional solution is root-monotone, $w_e \le w_{e(p)}$ (the standing property of the Section 11.1 LP solutions that the rounding rules presuppose, since $\delta_e/(w'_{e(p)}-w_e)$ must be a probability); edges processed in a topological order from the root, as the book prescribes; coin probabilities are clipped to $[0,1]$ inside the definition so that it is always a probability distribution — the clipping is inert under these hypotheses. Correction to the printed source: none.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 4(2-3), 2009, p. 229-230, Lemma 11.1 (Section 11.2)

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_marg
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree
import Definitions.Def_OnlinePrimalDual_GroupSteiner_roundRun_v2

namespace OnlinePrimalDual.GroupSteiner

/-- **Lemma 11.1** (Buchbinder & Naor, FnT TCS 2009, p. 230). The random cover
`roundCover tr ord δs` is the one the online rounding algorithm of Section 11.2 (p. 229-230)
actually produces — starting from the empty cover and the zero fractional solution, and running
one iteration per weight increment `δ ∈ δs`, each processing the edges whose weight increased in
the topological order `ord` (`hord`: a permutation of the edges in which every edge comes after
its parent edge, the book's "starting from the root") — rather than, as in the retired version,
an arbitrary distribution pinned by axioms that did not determine its marginals. The data are
the section's: increments are non-negative (`hδ`, the fractional solution only grows over time)
and every intermediate fractional solution is a flow from the root, `wₑ ≤ w_{e(p)}` along every
root path (`hflow`, the standing property of the LP solutions of Section 11.1 the rounding
rules presuppose, since the coin probability `δₑ/(w'_{e(p)} − wₑ)` must be at most `1`). The
conclusion is the lemma's, at the end of every iteration (every prefix of the increment sequence
is itself an admissible `δs`): writing `wₑ = fracWeight δs e` for the current weight, the
probability that `e ∈ C` equals `wₑ` whenever `wₑ ≤ 1`, and `e ∈ C` with probability `1` once
`wₑ > 1`. -/
theorem lemma11_1_v2 {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (ord : List E) (hord_nodup : ord.Nodup) (hord_mem : ∀ e, e ∈ ord)
    (hord : ∀ e p, tr.parent e = some p → ord.idxOf p < ord.idxOf e)
    (δs : List (E → ℝ)) (hδ : ∀ δ ∈ δs, ∀ e, 0 ≤ δ e)
    (hflow : ∀ T : ℕ, ∀ e p, tr.parent e = some p →
      fracWeight (δs.take T) e ≤ fracWeight (δs.take T) p) :
    (∀ e, fracWeight δs e ≤ 1 → (roundCover tr ord δs).marg e = fracWeight δs e) ∧
    (∀ e, 1 < fracWeight δs e → (roundCover tr ord δs).marg e = 1) := by sorry

end OnlinePrimalDual.GroupSteiner
