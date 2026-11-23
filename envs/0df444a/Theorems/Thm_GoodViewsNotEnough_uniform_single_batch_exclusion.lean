-- Prove2me | Theorems.Thm_GoodViewsNotEnough_uniform_single_batch_exclusion
-- name    : GoodViewsNotEnough.uniform_single_batch_exclusion
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:55:33.245244+00:00
-- url     : https://prove2.me/theorems/e172e742-b0d8-43d7-ae7e-0ed4d96054da
-- title:
--   Theorem 9: uniform single-batch exclusion
-- statement:
--   In the 512-dimensional model, draw one batch $\mathcal B$ of $N=256$ i.i.d. scenes with eight independent cube nuisances per scene, and fix it. Let
--
--   $$\widehat F_{\mathcal B}(h)=\frac1{NVk}\sum_{i,v}\|h_{iv}-\bar h_{i,G}\|^2+\frac1{50}\mathbb{E}_\theta\widehat R_{\mathcal B,\theta}(h),$$
--
--   where $h_{iv}=h(S_i,U_{iv})$ and $\bar h_{i,G}$ is the mean of the $G=2$ global views. The constraints are the population whitening constraints $\mathbb{E}h=0$, $\mathbb{E}hh^\top=I_{512}$. Let $r$ be a complete centred orthonormal scene basis. Then, with probability at least $0.828$ over $\mathcal B$:
--
--   1. every global minimiser of $\widehat F_{\mathcal B}$ over whitened encoders has strictly positive population nuisance fraction $u(h)>0$;
--   2. every minimiser of $\widehat F_{\mathcal B}(h_W)$ over the linear Stiefel class $W=[A,B]$, $WW^\top=I$, satisfies
--   $$u(W)=\frac{\|B\|_F^2}{512}>10^{-12}.$$
--
--   **Formalization Note** The theorem is stated for a fixed basis $r$, as in the setting of Appendix D.1. The global views are the first two of the eight views of each example.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Appendix E, Theorem 9, eqs. (28)-(29), p. 20

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex

namespace GoodViewsNotEnough

theorem uniform_single_batch_exclusion (r : Fin 513 → Fin 512 → ℝ)
    (hr : IsCenteredOrthonormalBasis r) :
    ENNReal.ofReal (828 / 1000) ≤ batchLaw {B |
      (∀ h, IsWhitenedHD h → IsMinOn (batchObjective B) {h | IsWhitenedHD h} h →
        0 < nuisanceFrac h) ∧
      (∀ W, IsStiefel W →
        IsMinOn (fun W => batchObjective B (linEncoder r W)) {W | IsStiefel W} W →
        nuisanceFrac (linEncoder r W) = (∑ a, ∑ b, W a (Sum.inr b) ^ 2) / 512 ∧
        1 / 10 ^ 12 < nuisanceFrac (linEncoder r W))} := by sorry

end GoodViewsNotEnough
