-- Prove2me | Theorems.Thm_MCTSBandit_NonstatUCB_peeling_event_inclusion
-- name    : MCTSBandit.NonstatUCB.peeling_event_inclusion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:55.364895+00:00
-- url     : https://prove2.me/theorems/087dbe68-0992-44d6-80ed-94256ea51465
-- title:
--   Equation (34) — two index events cap a pull count
-- statement:
--   Fix a suboptimal arm $i$, a horizon $n$, an integer $u\ge A(n)$, and a threshold $\tau$. Suppose $U_{i,u,t}\le\tau$ for each integer $t\in[u,n]$ and $U_{i_*,s,u+s}>\tau$ for each integer $s\in[1,n-u]$. Then
--
--   $$T_i(n)\le u.$$
--
--   This event inclusion converts index-tail estimates into a play-count tail estimate. The integer ranges are interpreted as empty when their endpoints cross.
-- source:
--   Shah, Xie & Xu, arXiv:1902.05213v4, p. 23, proof of Lemma 3, (34)

import Definitions.Def_MCTSBandit_NonstatUCB_UCB

namespace MCTSBandit.NonstatUCB

universe u

/-- Shah–Xie–Xu, implication (34), p. 23. -/
theorem peeling_event_inclusion {Ω : Type u} {K : ℕ}
    (X : Fin K → ℕ → Ω → ℝ) (I : ℕ → Ω → Fin K)
    (μ : Fin K → ℝ) (istar i : Fin K) (β ξ η α Δ : ℝ)
    (hβ : 1 < β) (hξ : 0 < ξ)
    (hη0 : (1 / 2 : ℝ) ≤ η) (hη1 : η < 1)
    (hα0 : ξ * η * (1 - η) ≤ α) (hα1 : α < ξ * (1 - η))
    (hα2 : 2 < α) (hgap : GapLB μ istar Δ)
    (hI : IsUCBRun X β ξ α η I) (hi : i ≠ istar)
    (n u : ℕ) (hu : Afun Δ β ξ α η n ≤ u) (τ : ℝ) (ω : Ω)
    (hE1 : ∀ t ∈ Finset.Icc u n, ucb X β ξ α η i u t ω ≤ τ)
    (hE2 : ∀ s ∈ Finset.Icc 1 (n - u), τ < ucb X β ξ α η istar s (u + s) ω) :
    pullCount I i n ω ≤ u := by sorry

end MCTSBandit.NonstatUCB
