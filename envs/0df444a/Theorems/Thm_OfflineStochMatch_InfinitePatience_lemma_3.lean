-- Prove2me | Theorems.Thm_OfflineStochMatch_InfinitePatience_lemma_3
-- name    : OfflineStochMatch.InfinitePatience.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:57.759182+00:00
-- url     : https://prove2.me/theorems/a7972007-ae4c-40d1-a45f-2b48552da48c
-- title:
--   Lemma 3, p. 11 — ∏_{f∈E₁(r)}(1 − x a(f) y_f) ≥ e^{−x Σ_{f∈E₁(r)} y_f} for an effective attenuation
-- statement:
--   Let $G=(V,E)$ be a graph with $p_f\in[0,1]$ and $y_f\in[0,1]$ for all edges, and let $\tilde a$ be an effective attenuation function (Definition 3), with $a(f)=\tilde a(p_fy_f)$. Fix an edge $e$, an endpoint $r$ of $e$, and $x\in[0,1]$. With $E_1(r)=\{f\in\delta(r)\setminus\{e\}:p_f=1\}$,
--   $$\prod_{f\in E_1(r)}\bigl(1-x\,a(f)\,y_f\bigr)\ \ge\ e^{-x\sum_{f\in E_1(r)}y_f}.$$
--
--   In the paper $x$ is the arrival time $\pi(e)$ on which the analysis conditions, and the product is the conditional probability that no edge of $E_1(r)$ blocks $e$ by being matched before it. The lemma turns that product into an exponential in the LP mass at $r$.
--
--   **Formalization Note.** The convexity in Definition 3 is assumed for $x\in(0,1)$; the statement covers the closed interval $[0,1]$ over which the paper integrates.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 11, Lemma 3 (E(r), E_b(r) defined just before)

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting

namespace OfflineStochMatch.InfinitePatience

/-- Lemma 3, p. 11: for an effective attenuation function, an endpoint `r` of `e` and `x ∈ [0,1]`,
`∏_{f ∈ E_1(r)} (1 - x a(f) y_f) ≥ e^{-x ∑_{f ∈ E_1(r)} y_f}`, where `a(f) = ã(p_f y_f)`. -/
theorem lemma_3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (aT : ℝ → ℝ)
    (haT : IsEffective aT) (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (hy : ∀ f, 0 ≤ y f ∧ y f ≤ 1)
    (e : E) (r : V) (hr : r ∈ G.ends e) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-(x * ∑ f ∈ E1 G p e r, y f))
      ≤ ∏ f ∈ E1 G p e r, (1 - x * aT (p f * y f) * y f) := by sorry

end OfflineStochMatch.InfinitePatience
