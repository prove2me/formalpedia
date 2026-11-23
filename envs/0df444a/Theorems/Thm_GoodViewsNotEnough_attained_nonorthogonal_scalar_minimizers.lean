-- Prove2me | Theorems.Thm_GoodViewsNotEnough_attained_nonorthogonal_scalar_minimizers
-- name    : GoodViewsNotEnough.attained_nonorthogonal_scalar_minimizers
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:51:09.151803+00:00
-- url     : https://prove2.me/theorems/b940a766-bcef-4575-a7d7-baf69302c791
-- title:
--   Theorem 1: attained nonorthogonal scalar minimizers
-- statement:
--   Consider the four-state scalar model, with observations $(S,U)\in\{\pm1\}^2$ under the uniform law, scene signs $s=(1,1,-1,-1)$ and pair law $\pi_{ij}=(1+s_is_j/2)/16$. Let
--
--   $$F_\pi(x)=\frac14\sum_{i,j}\pi_{ij}(x_i-x_j)^2+\frac1{49}R_{1024,\rm gr}(\mu_x),\qquad\mu_x=\frac14\sum_i\delta_{x_i},$$
--
--   where $R_{1024,\rm gr}(\mu)$ is the exact expectation of the Epps–Pulley statistic $1024\,D_{\rm gr}(\hat\mu_{1024})$ on an i.i.d. batch of size $1024$ from $\mu$. Here $D_{\rm gr}$ is the 17-node grid discrepancy, with nodes $t_j=5j/8$ and weights $\omega_j=\frac58c_je^{-t_j^2/2}$. Then, on the centred domain $X_0=\{x\in\mathbb{R}^4:\sum_ix_i=0\}$:
--
--   1. $F_\pi$ attains its minimum on $X_0$;
--   2. every global minimiser $x$ takes distinct values within at least one scene: $x_1\ne x_2$ or $x_3\ne x_4$;
--   3. for every global minimiser $x$, exchanging the two observations of one scene gives a point $x\circ T$ ($T=(12)$ or $(34)$) that is again a global minimiser with $F_\pi(x\circ T)=F_\pi(x)$ and $x\circ T\notin\{x,-x\}$.
--
--   The positive-pair relation of this model lies entirely in the scenes, so good views alone would favour scene-only encoders. The theorem shows that the Gaussian regulariser makes every global optimum retain nuisance, and that the optimum is not unique up to rotation.
--
--   **Formalization Note** The paper averages the Epps–Pulley term over two views. Each view has marginal law $\mu_x$, so the average equals $R_{1024,\rm gr}(\mu_x)$, which is the form used here.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Section 4, Theorem 1, eq. (1), p. 4; proof in Appendix B.3

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex

namespace GoodViewsNotEnough

theorem attained_nonorthogonal_scalar_minimizers :
    (∃ x ∈ centeredDomain, IsMinOn (scalarObjective scalarPairLaw) centeredDomain x) ∧
    (∀ x ∈ centeredDomain, IsMinOn (scalarObjective scalarPairLaw) centeredDomain x →
      x 0 ≠ x 1 ∨ x 2 ≠ x 3) ∧
    (∀ x ∈ centeredDomain, IsMinOn (scalarObjective scalarPairLaw) centeredDomain x →
      ∃ T ∈ sceneSwaps, x ∘ ⇑T ∈ centeredDomain ∧
        IsMinOn (scalarObjective scalarPairLaw) centeredDomain (x ∘ ⇑T) ∧
        scalarObjective scalarPairLaw (x ∘ ⇑T) = scalarObjective scalarPairLaw x ∧
        x ∘ ⇑T ≠ x ∧ x ∘ ⇑T ≠ -x) := by sorry

end GoodViewsNotEnough
