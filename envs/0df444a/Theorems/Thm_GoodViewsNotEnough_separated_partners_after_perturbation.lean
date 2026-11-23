-- Prove2me | Theorems.Thm_GoodViewsNotEnough_separated_partners_after_perturbation
-- name    : GoodViewsNotEnough.separated_partners_after_perturbation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:52:39.459186+00:00
-- url     : https://prove2.me/theorems/dd8b8014-0490-4184-b462-42fbb1c32cc9
-- title:
--   Corollary 6: explicit separated partners after perturbation
-- statement:
--   Let $\pi'$ be a symmetric pair law on the four observations, with nonnegative entries and uniform marginals $\sum_j\pi'_{ij}=\frac14$, and suppose
--
--   $$\varepsilon=\sum_{i,j}|\pi'_{ij}-\pi_{ij}|\le\frac1{200000}.$$
--
--   Let $F_{\pi'}=P_{\pi'}+R_{1024,\rm gr}/49$ on $X_0$. Then every global minimiser $y$ of $F_{\pi'}$ on $X_0$ has a within-scene swap $z=Ty$, $T\in\{T_+,T_-\}$, with
--
--   $$d_\pm(y,z)>\frac1{40},\qquad0\le F_{\pi'}(z)-\min F_{\pi'}<\frac3{100000}.$$
--
--   More precisely, the excess is at most $16\varepsilon\tau H_0$, where $\tau=(1+8\varepsilon)/(1-8\varepsilon)$ and $H_0=\frac{184273}{500000}$.
--
--   So after a small perturbation of the pair law, each optimum still has a near-optimal partner that is separated from its sign orbit.
--
--   **Formalization Note** Since $y$ is a global minimiser, $\min F_{\pi'}=F_{\pi'}(y)$, and the excess is written as $F_{\pi'}(z)-F_{\pi'}(y)$.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Appendix C, Corollary 6, pp. 15-16

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex

namespace GoodViewsNotEnough

theorem separated_partners_after_perturbation (π' : Fin 4 → Fin 4 → ℝ) (hπ' : IsUniformPairLaw π')
    (hε : ∑ i, ∑ j, |π' i j - scalarPairLaw i j| ≤ 1 / 200000) :
    ∀ y ∈ centeredDomain, IsMinOn (scalarObjective π') centeredDomain y →
      ∃ T ∈ sceneSwaps, 1 / 40 < signOrbitDist y (y ∘ ⇑T) ∧
        0 ≤ scalarObjective π' (y ∘ ⇑T) - scalarObjective π' y ∧
        scalarObjective π' (y ∘ ⇑T) - scalarObjective π' y < 3 / 100000 ∧
        scalarObjective π' (y ∘ ⇑T) - scalarObjective π' y ≤
          16 * (∑ i, ∑ j, |π' i j - scalarPairLaw i j|) *
            ((1 + 8 * ∑ i, ∑ j, |π' i j - scalarPairLaw i j|) /
              (1 - 8 * ∑ i, ∑ j, |π' i j - scalarPairLaw i j|)) * (184273 / 500000) := by sorry

end GoodViewsNotEnough
