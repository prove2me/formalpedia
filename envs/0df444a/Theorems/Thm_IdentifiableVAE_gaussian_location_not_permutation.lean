-- Prove2me | Theorems.Thm_IdentifiableVAE_gaussian_location_not_permutation
-- name    : IdentifiableVAE.gaussian_location_not_permutation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:01:04.117494+00:00
-- url     : https://prove2.me/theorems/d8e979a9-28fa-4833-9497-66d57a8a50c8
-- title:
--   Proposition 1 (as proved): Gaussian location families are not $\sim_P$-identifiable
-- statement:
--   Let $k=1$ and $n\ge2$. Let $\theta=(f,Q,T,\lambda)$ describe a model on $U$ with Gaussian base measure $Q_i(t)=e^{-t^2}$ and sufficient statistic $T_i(t)=t$ for all $i$, so that only the location of each $z_i$ depends on $u$. Then there is a parameter $\tilde\theta$ describing a model on $U$ with
--
--   $$p_{\tilde\theta}(x\mid u)=p_\theta(x\mid u)\qquad(u\in U),$$
--
--   such that $\theta\not\sim_P\tilde\theta$, even in the almost-everywhere sense. The matrix $A$ of Theorem 1 therefore cannot be reduced to a permutation matrix. The competing parameter is obtained from an orthogonal transformation of the latents: $\tilde f=f\circ R^\top$, $\tilde\lambda=R\lambda$.
--
--   **Formalization Note** The case $Q_i\equiv1$ of the paper is not included. With $T_i(t)=t$ on $\mathbb{R}$ the factor $e^{\lambda t}$ is never integrable, and on a half-line the rotation used in the proof does not preserve the domain. The hypothesis $n\ge2$ is added: for $n=1$ every invertible $1\times1$ matrix is a permutation block, so $\sim_A$ and $\sim_P$ coincide and Theorem 1 contradicts the claim whenever its hypotheses hold. (For $n=1$ with $\lambda$ constant on $U$, the claim does hold, through a non-affine measure-preserving rearrangement of the latent.)
-- source:
--   Khemakhem, Kingma, Monti and Hyvärinen, Variational Autoencoders and Nonlinear ICA: A Unifying Framework, AISTATS 2020, arXiv:1907.04809v4, Section 4.2, Proposition 1, p. 6; proof in Appendix B.5, eqs. (48)-(52), pp. 17-18

import Mathlib
import Definitions.Def_IdentifiableVAE_Basic

open MeasureTheory

namespace IdentifiableVAE

theorem gaussian_location_not_permutation {n d m : ℕ} (hn : 2 ≤ n) (hnd : n ≤ d)
    (U : Set (Fin m → ℝ))
    (Pε : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pε] (hPε : Pε ≪ volume)
    (θ : Param n d m 1) (hθ : IsParam θ U)
    (hT : ∀ i t, θ.T i 0 t = t) (hQ : ∀ i t, θ.Q i t = Real.exp (-t ^ 2)) :
    ∃ θ' : Param n d m 1, IsParam θ' U ∧ (∀ u ∈ U, obsLaw Pε θ u = obsLaw Pε θ' u) ∧
      ¬ SimPAE θ θ' := by sorry

end IdentifiableVAE
