-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_switching_lemma_dnf
-- name    : HypercliqueAC0.FixedDepth.switching_lemma_dnf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T00:59:36.886695+00:00
-- url     : https://prove2.me/theorems/50f6ccbc-85c6-59aa-bb26-7f855ad7a93e
-- title:
--   Håstad's switching lemma for DNFs: $\Pr[\mathrm{DT}(F|_\rho)>t]\le(16pw)^t$
-- statement:
--   Let $X$ be a finite set, let $F$ be a DNF over the variables $(x_e)_{e\in X}$ whose terms all have width at most $w$, and let $\rho\sim\mathcal R_p$ be a $p$-random restriction, which leaves every coordinate free with probability $p$ and fixes it to $0$ or to $1$ with probability $(1-p)/2$ each, independently. If $0\le p\le 1/2$, then for every integer $t\ge0$
--
--   $$\Pr_{\rho\sim\mathcal R_p}\bigl[\mathrm{DT}(F|_\rho)>t\bigr]\le(16pw)^t,$$
--
--   where $\mathrm{DT}$ denotes decision-tree depth.
--
--   This is Håstad's switching lemma with an explicit constant: after a random restriction with star probability $p=\Theta(1/w)$, a width-$w$ DNF collapses, except with probability exponentially small in $t$, to a function of decision-tree depth at most $t$. Applied layer by layer it shows that constant-depth circuits simplify under random restrictions, which yields Fourier tail bounds for them.
--
--   **Formalization Note** Terms are finite sets of literals; a term containing both $x_e$ and $\neg x_e$ is allowed and is never satisfied.
-- source:
--   Håstad, Almost optimal lower bounds for small depth circuits, STOC 1986, Lemma 1; Razborov's encoding proof as in Beame, A switching lemma primer (1994), Lemma 1 (stated there with constant 7); used in Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/830.pdf, §3.4 via [Tal17, Theorem 18] (Theorem 3.2).

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting
import Definitions.Def_HypercliqueAC0_FixedDepth_Switching

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

theorem switching_lemma_dnf {X : Type} [Fintype X] (w t : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (F : Finset (Finset (X × Bool))) (hF : ∀ T ∈ F, T.card ≤ w) :
    restrictionProb p (fun ρ => ¬ DTDepthLE t (restrictFn ρ (dnfValue F))) ≤
      (16 * p * (w : ℝ)) ^ t := by sorry

end HypercliqueAC0.FixedDepth
