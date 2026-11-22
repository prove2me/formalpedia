-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_bipartiteCoreCertificate
-- name    : HodgeComputer.FourPlusTwoResidual.bipartiteCoreCertificate
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:37.694174+00:00
-- url     : https://prove2.me/theorems/4341466c-3ef6-4249-8e58-48a91f72894d
-- title:
--   Existence of an even-degree (Z/2 x Z/2)-bipartite four-variable core certificate
-- statement:
--   Let $H(x_0, x_1, y_0, y_1)$ be the four-variable sextic core of `four-plus-two-residual` and let $A = x_0^3 y_0^3$. There exist a nonzero homogeneous polynomial $D \in \mathbb{C}[x_0, x_1, y_0, y_1]$ of **even** positive degree $2m + 2$ and homogeneous polynomials $N_0, N_1, N_2, N_3$ of degree $2m + 3$ such that:
--
--   1. $D$ is invariant under both $\sigma_{AB}(x_0, x_1, y_0, y_1) = (-x_0, -x_1, y_0, y_1)$ and $\sigma_{CD}(x_0, x_1, y_0, y_1) = (x_0, x_1, -y_0, -y_1)$;
--   2. $(N_0, N_1)$ is $\sigma_{AB}$-even and $(N_2, N_3)$ is $\sigma_{AB}$-odd;
--   3. $(D, N)$ satisfies the exact four-variable core identity
--
--   $$
--   2 A D^2 - 2 D \sum_{i=0}^3 (\partial_i H) N_i + 3 H \Bigl(D \sum_{i=0}^3 \partial_i N_i - \sum_{i=0}^3 (\partial_i D) N_i\Bigr) = 0.
--   $$
--
--   By `coreCertificate_iff_bipartite` and `normalChart_residue_of_coreCertificate`, this symmetry-reduced four-variable existence statement implies **both** open mission frontier targets `coreCertificate` and `normalChart_residue_solvable`, and hence the root target `HodgeComputer.FourPlusTwoResidual.certificate`.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` (`docs/03b-weighted-threefolds.md`) and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry

theorem HodgeComputer.FourPlusTwoResidual.bipartiteCoreCertificate :
    ∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.BipartiteCoreCertificate D N := by sorry
