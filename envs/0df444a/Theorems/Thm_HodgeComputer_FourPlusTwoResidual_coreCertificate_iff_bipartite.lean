-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate_iff_bipartite
-- name    : HodgeComputer.FourPlusTwoResidual.coreCertificate_iff_bipartite
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:32.376952+00:00
-- url     : https://prove2.me/theorems/869e4fa2-7a9d-4b62-a2a5-3a7fe862452b
-- title:
--   Equivalence of unrestricted and even-degree (Z/2 x Z/2)-bipartite core certificates
-- statement:
--   The four-variable core problem `∃ D N, CoreCertificate D N` for `four-plus-two-residual` is equivalent to the existence of an even-degree $(\mathbb{Z}/2 \times \mathbb{Z}/2)$-equivariant `BipartiteCoreCertificate`:
--
--   $$
--   \bigl(\exists D, N,\; \operatorname{CoreCertificate}(D, N)\bigr) \;\Longleftrightarrow\; \bigl(\exists \widehat{D}, \widehat{N},\; \operatorname{BipartiteCoreCertificate}(\widehat{D}, \widehat{N})\bigr).
--   $$
--
--   Specifically, given any core certificate $(D, N)$ of arbitrary degree $k + 1 \ge 1$, its negated pullback $(D', N') = (\sigma_{AB}^* D,\; (\sigma_{AB}^* N_0, \sigma_{AB}^* N_1, -\sigma_{AB}^* N_2, -\sigma_{AB}^* N_3))$ under $\sigma_{AB}(x_0, x_1, y_0, y_1) = (-x_0, -x_1, y_0, y_1)$ is again a core certificate because $\sigma_{AB}^* H = H$ and $\sigma_{AB}^* A = -A$. Clearing denominators of the rational average $\frac{1}{2}(N/D + N'/D')$ produces
--
--   $$
--   \widehat{D} = 2 D D', \qquad \widehat{N}_i = D' N_i + D N'_i,
--   $$
--
--   which is automatically **nonzero** ($2 D D' \neq 0$ in the integral domain $\mathbb{C}[x_0, x_1, y_0, y_1]$, bypassing the vanishing hazard of naive linear symmetrization when $\sigma_{AB}^* D = -D$), has even degree $2k + 2$, is invariant under both $\sigma_{AB}$ and $\sigma_{CD}$ (since $(\sigma_{AB} \circ \sigma_{CD})^* \widehat{D} = (-1)^{2k+2} \widehat{D} = \widehat{D}$), and satisfies the exact $(+1, +1, -1, -1)$ bipartite numerator parity.
--
--   **Formalization Note** Halves the symmetry sectors of the open leaf `coreCertificate` without losing existence.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry

theorem HodgeComputer.FourPlusTwoResidual.coreCertificate_iff_bipartite :
    (∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.CoreCertificate D N) ↔
    (∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.BipartiteCoreCertificate D N) := by sorry
