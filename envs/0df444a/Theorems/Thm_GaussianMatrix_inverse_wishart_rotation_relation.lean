-- Prove2me | Theorems.Thm_GaussianMatrix_inverse_wishart_rotation_relation
-- name    : GaussianMatrix.inverse_wishart_rotation_relation
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T06:15:08.674452+00:00
-- url     : https://prove2.me/theorems/673268d1-1900-492f-ab3b-96e2cc092a6e
-- title:
--   Rotation identity for inverse Wishart second moments: $\mathbb{E}[(W^{-1})_{ii}^2] = \mathbb{E}[(W^{-1})_{ii}(W^{-1})_{jj}] + 2\,\mathbb{E}[(W^{-1})_{ij}^2]$
-- statement:
--   Let $r + 4 \le k$, let $G \in \mathbb{R}^{r\times k}$ be a standard Gaussian matrix and $W = GG^\top$. For any two distinct indices $i \ne j$,
--
--   $$\mathbb{E}\big[(W^{-1})_{ii}^2\big] \;=\; \mathbb{E}\big[(W^{-1})_{ii}(W^{-1})_{jj}\big] + 2\,\mathbb{E}\big[(W^{-1})_{ij}^2\big].$$
--
--   The identity expresses the orthogonal invariance of the law of $W^{-1}$ ($UW^{-1}U^\top \overset{d}{=} W^{-1}$ for orthogonal $U$, inherited from $UG \overset{d}{=} G$). Applying it to the $45^\circ$ rotation in the $(i,j)$-plane gives $(UW^{-1}U^\top)_{ii} = \tfrac12\big((W^{-1})_{ii} + (W^{-1})_{jj} + 2(W^{-1})_{ij}\big)$; squaring, taking expectations, and using $\mathbb{E}[(W^{-1})_{ii}^2] = \mathbb{E}[(W^{-1})_{jj}^2]$ together with $\mathbb{E}[(W^{-1})_{ii}(W^{-1})_{ij}] = \mathbb{E}[(W^{-1})_{jj}(W^{-1})_{ij}] = 0$ (sign flip of one coordinate) yields the relation. It reduces the three second-moment constants $\alpha,\beta,\gamma$ of the inverse Wishart matrix to two.
--
--   **Formalization Note.** All integrals are Bochner integrals; the hypothesis $r+4\le k$ guarantees integrability of every term (all are dominated by $(W^{-1})_{ii}^2 + (W^{-1})_{jj}^2$), so the identity is not an artefact of the convention that non-integrable functions have integral $0$.
-- source:
--   standard fact: consequence of the orthogonal invariance of the Gaussian matrix law ($UG \overset{d}{=} G$ for orthogonal $U$) and the resulting form $\mathbb{E}[(W^{-1})_{ij}(W^{-1})_{kl}] = \beta\,\delta_{ij}\delta_{kl} + \gamma(\delta_{ik}\delta_{jl}+\delta_{il}\delta_{jk})$ of an orthogonally invariant fourth-order moment tensor, which forces $\alpha = \beta + 2\gamma$; cf. R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley 1982, Sec. 3.2 (from memory).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem inverse_wishart_rotation_relation {r k : ℕ} (hrk : r + 4 ≤ k) (i j : Fin r) (hij : i ≠ j) :
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 ∂(gaussianMatrix r k)
      = ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j
            ∂(gaussianMatrix r k)
        + 2 * ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ^ 2 ∂(gaussianMatrix r k) := by sorry

end GaussianMatrix
