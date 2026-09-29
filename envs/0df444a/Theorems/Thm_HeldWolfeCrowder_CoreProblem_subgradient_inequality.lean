-- Prove2me | Theorems.Thm_HeldWolfeCrowder_CoreProblem_subgradient_inequality
-- name    : HeldWolfeCrowder.CoreProblem.subgradient_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:48:58.050786+00:00
-- url     : https://prove2.me/theorems/4a8f8bda-5681-4443-8821-9b825343775b
-- title:
--   Eq. (2.10) — the selected v_k is a supergradient: w* − w(π) ≤ v_k·(π* − π)
-- statement:
--   Let $w(\pi)=\min_k\{c_k+\pi\cdot v_k\}$ be the piecewise-linear concave function (2.2) on $E^n$, and let $\pi^*$ be any point of the optimal set, $w(\pi^*)=w^*=\max w$. If the index $k$ attains the minimum in (2.2) at a point $\pi$ (for instance $\pi=\pi^j$ and $k=k(j)$, the index chosen at step $j$ of the subgradient algorithm), then
--   $$w^*-w(\pi)\le v_k\cdot(\pi^*-\pi).$$
--
--   This is relation (2.4) applied to the subgradient $v(\pi^j)=v_{k(j)}\in\partial w(\pi^j)$: when $\pi^j$ is not optimal, the direction $v(\pi^j)$ makes an acute angle with the ray from $\pi^j$ through $\pi^*$. It is the basic inequality behind every convergence proof for the method.
--
--   **Formalization Note** The statement is given for an arbitrary point $\pi$ and any index attaining the minimum there; the paper's display is the case $\pi=\pi^j$, $k=k(j)$. "$\pi^*$ optimal" is the hypothesis that $w(\pi')\le w(\pi^*)$ for every $\pi'$.
-- source:
--   Held, Wolfe & Crowder, Validation of subgradient optimization, Math. Programming 6 (1974), p. 67, Eq. (2.10)

import Mathlib
import Definitions.Def_HeldWolfeCrowder_CoreProblem_Setting

namespace HeldWolfeCrowder.CoreProblem

open scoped InnerProductSpace
open Filter Topology

/-- **Held, Wolfe & Crowder (1974), Eq. (2.10), p. 67.** Let `π*` be a maximizer of `w`
(`w(π*) = w* = max w`). If the index `k` attains the minimum (2.2) at `π` (so
`v_k ∈ V(π) ⊆ ∂w(π)`; in particular for `π = π^j`, `k = k(j)`), then
`w* − w(π) ≤ v_k · (π* − π)`. -/
theorem subgradient_inequality {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n))
    (πstar : EuclideanSpace ℝ (Fin n)) (hstar : ∀ π', w c v π' ≤ w c v πstar)
    (π : EuclideanSpace ℝ (Fin n)) (k : ι) (hk : IsMinIndex c v π k) :
    w c v πstar - w c v π ≤ ⟪v k, πstar - π⟫_ℝ := by sorry

end HeldWolfeCrowder.CoreProblem
