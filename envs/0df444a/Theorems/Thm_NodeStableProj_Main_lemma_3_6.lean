-- Prove2me | Theorems.Thm_NodeStableProj_Main_lemma_3_6
-- name    : NodeStableProj.Main.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:58:51.507195+00:00
-- url     : https://prove2.me/theorems/7849a07c-12be-4c95-9dc9-ad7eb62ff4cc
-- title:
--   Lemma 3.6 — accuracy of the SVT counter: with probability ≥ 1 − β all Laplace noises are below k/2 and every detector is ⊥ below τ − k and ⊤ from τ + k
-- statement:
--   There is an absolute constant $c_1>0$ such that the following holds. Let $n\in\mathbb N$, let $G=(V,E)$ be a graph with $|V|\le n$, let $\beta\in(0,1/2)$, and run Algorithm 1 on $G$ with integers $0<D<\hat D$ and $\tilde\varepsilon>0$, so each vertex $u$ has an SVT detector $t(u)$ with threshold $\tau=(D+\hat D)/2$, threshold noise $\eta_u\sim\mathrm{Lap}(2/\tilde\varepsilon)$ and query noise $\xi_{u,\ell}\sim\mathrm{Lap}(4/\tilde\varepsilon)$ for its $\ell$-th increment. Put
--   $$k=\frac{c_1\log(n/\beta)}{\tilde\varepsilon}.$$
--   Then with probability at least $1-\beta$, simultaneously for all $u\in V$:
--   1. $|\eta_u|<k/2$ and $|\xi_{u,\ell}|<k/2$ for every call $\ell\in[|V|-1]$ to increment on $t(u)$;
--   2. at every time step of the main loop, the flag of $t(u)$ is $\bot$ if its count is below $\tau-k$;
--   3. at every time step, the flag of $t(u)$ is $\top$ if its count is at least $\tau+k$.
--
--   This is the accuracy half of the SVT detector analysis; Lemma 3.3 uses it to bound the probability of the fallback and of the complement of $\mathrm{Good}_{v^*}$.
--
--   Differences from the source:
--   - reading: all β < 1/2 → β ∈ (0, 1/2); reason: log(n/β) is undefined for β ≤ 0
--   - encoding: detectors with parameter ε, k = c1 log(n/β)/ε → the detectors of Algorithm 1 run on G with parameters 0 < D < D̂ (τ = (D + D̂)/2) and ε̃ > 0, k = c1 log(n/β)/ε̃, natural log; reason: the lemma writes ε for the detectors' parameter ε̃ of Algorithm 1, the setting in which it is stated and used
--   - encoding: "at all time steps" → every state of the main loop (after 0, 1, …, all pairs), noises presampled with ξ_{u,ℓ} the noise of the ℓ-th call; reason: the paper's own presampling (p. 14); a call after the flag is raised draws nothing, so the law is unchanged
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 13, Lemma 3.6

import Mathlib
import Definitions.Def_NodeStableProj_Main_Projection

open MeasureTheory

namespace NodeStableProj.Main

/-- Lemma 3.6 (Accuracy of SVT Counter), p. 13: there is `c1 > 0` such that for all `n`, all
graphs with `|V| ≤ n`, all `β ∈ (0, 1/2)` and all parameters of Algorithm 1, with probability at
least `1 − β` every Laplace noise of every detector is below `k/2` in absolute value and every
detector is `⊥` while `count < τ − k` and `⊤` while `count ≥ τ + k`, `k = c1 log(n/β)/ε̃`. -/
theorem lemma_3_6 : ∃ c1 : ℝ, 0 < c1 ∧ SVTAccuracy c1 := by sorry

end NodeStableProj.Main
