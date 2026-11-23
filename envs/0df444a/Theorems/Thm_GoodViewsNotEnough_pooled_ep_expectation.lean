-- Prove2me | Theorems.Thm_GoodViewsNotEnough_pooled_ep_expectation
-- name    : GoodViewsNotEnough.pooled_ep_expectation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:54:23.339698+00:00
-- url     : https://prove2.me/theorems/1c7c75e3-9499-4c54-9444-f10db3f3e872
-- title:
--   Eq. (20): exact expectation of the pooled Epps–Pulley statistic
-- statement:
--   In the 512-dimensional model, let $h(S,U)\in\mathbb{R}^{512}$ be any encoder. Let $\mathcal B$ be a batch of $N=256$ i.i.d. scenes, each with $V=8$ independent nuisances, so that there are $M=2048$ outputs. Let $\theta$ be uniform on $\mathbb{S}^{511}$. Write
--
--   - $A_\nu=\sum_j\omega_j$ and $C_\nu=\sum_j\omega_jg_j^2$;
--   - $J(h)=\sum_j\omega_j\mathbb{E}_\theta|\varphi_{h,\theta}(t_j)|^2$ and $J_c(h)=\sum_j\omega_j\mathbb{E}_{S,\theta}|\varphi_{h\mid S,\theta}(t_j)|^2$;
--   - $X(h)=\sum_j\omega_jg_j\,\mathbb{E}_\theta\operatorname{Re}\varphi_{h,\theta}(t_j)$.
--
--   Here $\varphi_{h,\theta}$ and $\varphi_{h\mid S,\theta}$ are the marginal and the conditional characteristic functions of $\theta^\top h$. Then the pooled statistic has expectation
--
--   $$\bar R(h)=\mathbb{E}_{\mathcal B,\theta}\widehat R_{\mathcal B,\theta}(h)=(M-V)J+(V-1)J_c-2MX+MC_\nu+A_\nu.$$
--
--   The within-example term $J_c$ is what distinguishes the pooled statistic from one computed on $M$ unrelated observations.
--
--   **Formalization Note** Only the second line of eq. (20) is stated. The first line, $MD+(A_\nu-J)+(V-1)(J_c-J)$ with $D=J-2X+C_\nu$, is the same expression rearranged.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Appendix D.2, eqs. (19)-(20), p. 17

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex

namespace GoodViewsNotEnough

theorem pooled_ep_expectation (h : Fin 513 → (Fin 512 → Bool) → Fin 512 → ℝ) :
    pooledEP h = (2048 - 8) * pooledJ h + (8 - 1) * pooledJc h - 2 * 2048 * pooledX h +
      2048 * (∑ j, pooledWeight j * gaussCF (pooledNode j) ^ 2) + ∑ j, pooledWeight j := by sorry

end GoodViewsNotEnough
