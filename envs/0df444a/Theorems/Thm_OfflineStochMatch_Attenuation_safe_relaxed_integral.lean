-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_safe_relaxed_integral
-- name    : OfflineStochMatch.Attenuation.safe_relaxed_integral
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-16T08:22:50.776373+00:00
-- url     : https://prove2.me/theorems/c87dd9ec-5739-426e-9642-e361f405ae2e
-- title:
--   §3.2 p. 11 — the random-order probability of both one-sided relaxed events equals the integral of the product of one-sided probabilities
-- statement:
--   Let $G=(V,E)$ be a finite loopless graph without parallel edges ($\mathrm{ends}$ injective) and let $e=\{u,v\}$ be an edge. Take arbitrary real vectors $p,y$, patiences $t$ and a function $\tilde a$ (no range assumptions are needed: the identity is algebraic). Then
--   $$\Pr_{\sigma,Y,A,P}\big[\mathrm{SideOK}_u(B^\sigma,Y,A,P)\wedge \mathrm{SideOK}_v(B^\sigma,Y,A,P)\big]=\int_0^1 \mathrm{sideProb}_u(x)\,\mathrm{sideProb}_v(x)\,dx .$$
--   Here $B^\sigma$ = `arrivedBefore σ e` marks the edges processed before $e$, and on the left $\sigma$ is a uniformly random order of $E$ while the coins have the Bernoulli weights of `prob` in the Setting.
--
--   This is the probabilistic step on p. 11 of the paper. A uniformly random order is the same as i.i.d. uniform arrival times $\pi(f)\in[0,1]$. Given $\pi(e)=x$, each other edge arrives before $e$ independently with probability $x$. The two one-sided events depend on the disjoint edge sets $E(u)$ and $E(v)$: they are disjoint because $G$ has no parallel edges. So they are conditionally independent, and integrating over $x$ gives the right-hand side. In the finite model: for a fixed set $S\subseteq E\setminus\{e\}$, the probability that the set of edges before $e$ is exactly $S$ is $|S|!\,(|E|-1-|S|)!/|E|!=\int_0^1 x^{|S|}(1-x)^{|E|-1-|S|}dx$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §3.2 p. 11: conditioning on the arrival time of e and factorizing over the two endpoints (display before Lemma 3), giving Eq. (8)

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting
import Definitions.Def_OfflineStochMatch_Attenuation_SideProb

namespace OfflineStochMatch.Attenuation

theorem safe_relaxed_integral {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Function.Injective G.ends)
    (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ) (e : E) (u v : V) (huv : G.ends e = s(u, v)) :
    prob p y (attProb aT p y) (fun σ Y A P =>
        SideOK G t e u (arrivedBefore σ e) Y A P ∧ SideOK G t e v (arrivedBefore σ e) Y A P) =
      ∫ x in (0 : ℝ)..1, sideProb G p t y aT e u x * sideProb G p t y aT e v x := by sorry

end OfflineStochMatch.Attenuation
