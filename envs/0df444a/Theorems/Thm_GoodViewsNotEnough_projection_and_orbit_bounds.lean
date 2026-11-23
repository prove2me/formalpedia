-- Prove2me | Theorems.Thm_GoodViewsNotEnough_projection_and_orbit_bounds
-- name    : GoodViewsNotEnough.projection_and_orbit_bounds
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:51:47.235998+00:00
-- url     : https://prove2.me/theorems/a144290d-f68b-4afe-a70a-4b60e4b2b0bc
-- title:
--   Lemma 5: projection and orbit bounds
-- statement:
--   Let $F_\pi=P_\pi+R_{1024,\rm gr}/49$ on $X_0$ be the objective of Theorem 1. Put $H_0=\frac{184273}{500000}$, $B_0=\frac{1024}{2450}$ and $L_0=\frac{345459}{4900}$, and let $u(x)=\mathbb{E}\operatorname{Var}(x\mid S)$. Then:
--
--   1. $F_\pi(w)<H_0$ for the comparator $w$;
--   2. for every $x\in X_0$,
--   $$B_0<F_\pi(\mathbb{E}[x\mid S])\le F_\pi(x)+L_0\,u(x);$$
--   3. if $m_*=\min_{X_0}F_\pi$, $x\in X_0$ and $F_\pi(x)-m_*\le\delta$, then
--   $$\max_{T\in\{T_+,T_-\}}d_\pm(x,Tx)^2\ge2u(x)-24\delta,$$
--   where $d_\pm(x,z)=\min\{\|x-z\|_p,\|x+z\|_p\}$ and $\|x\|_p^2=\frac14\sum_ix_i^2$;
--   4. every global minimiser of $F_\pi$ on $X_0$ has $u>\frac7{10000}$.
--
--   **Formalization Note** $m_*$ is written as the infimum of $F_\pi$ over $X_0$, which equals the minimum because Theorem 1 shows that it is attained.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Appendix C, Lemma 5, eqs. (14)-(15), p. 15

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex

namespace GoodViewsNotEnough

theorem projection_and_orbit_bounds :
    scalarObjective scalarPairLaw scalarComparator < 184273 / 500000 ∧
    (∀ x ∈ centeredDomain,
      1024 / 2450 < scalarObjective scalarPairLaw (sceneCondMean x) ∧
      scalarObjective scalarPairLaw (sceneCondMean x) ≤
        scalarObjective scalarPairLaw x + 345459 / 4900 * scalarNuisance x) ∧
    (∀ (δ : ℝ), ∀ x ∈ centeredDomain,
      scalarObjective scalarPairLaw x - sInf (scalarObjective scalarPairLaw '' centeredDomain) ≤ δ →
      2 * scalarNuisance x - 24 * δ ≤
        max (signOrbitDist x (x ∘ ⇑(Equiv.swap (0 : Fin 4) 1)) ^ 2)
          (signOrbitDist x (x ∘ ⇑(Equiv.swap (2 : Fin 4) 3)) ^ 2)) ∧
    (∀ x ∈ centeredDomain, IsMinOn (scalarObjective scalarPairLaw) centeredDomain x →
      7 / 10000 < scalarNuisance x) := by sorry

end GoodViewsNotEnough
