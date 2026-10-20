-- Prove2me | Theorems.Thm_FrobMednykh_mednykh
-- name    : FrobMednykh.mednykh
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-19T19:16:35.291029+00:00
-- url     : https://prove2.me/theorems/cb7c6904-53b4-42d9-bc51-cff32ae901ee
-- title:
--   Mednykh's formula for closed orientable surfaces
-- statement:
--   $G$ is a finite group; representations are finite-dimensional over $\mathbb C$ (`FDRep ℂ G`), $\chi_V$ is the character and $d_V=\dim V$. An `IrrepFamily G ι` is a family $(V_i)_{i\in\iota}$ of irreducible representations, pairwise non-isomorphic, such that every irreducible representation is isomorphic to some $V_i$; $d_i=\dim V_i$, $\chi_i=\chi_{V_i}$. $\Gamma_g$ (`SurfaceGroup g`) is the presented group $\langle a_1,b_1,\dots,a_g,b_g\mid [a_1,b_1]\cdots[a_g,b_g]\rangle$, the standard presentation of $\pi_1$ of the closed orientable genus-$g$ surface. For every $g\ge0$: $\sum_i d_i^{\,2-2g}=|G|^{\,1-2g}\,\#\mathrm{Hom}(\Gamma_g,G)$, i.e. $\sum_{V\in\hat G}d(V)^{\chi(\Sigma_g)}=|G|^{\chi(\Sigma_g)-1}\#\mathrm{Hom}(\pi_1\Sigma_g,G)$.
-- source:
--   M. Mulase, J. T. Yu, A generating function of the number of homomorphisms from a surface group into a finite group, arXiv:math/0209008 (2002), https://arxiv.org/abs/math/0209008, Theorem 1.1, eq. (1.1); N. Snyder, Mednykh's formula via lattice topological quantum field theories, arXiv:math/0703073 (2007), https://arxiv.org/abs/math/0703073, eq. (1); A. D. Mednykh, Dokl. Akad. Nauk SSSR 239 (1978)

import Definitions.Def_FrobMednykh_defs

open CategoryTheory

namespace FrobMednykh

theorem mednykh {G ι : Type} [Group G] [Fintype G] [Fintype ι]
    (B : IrrepFamily G ι) (g : ℕ) :
    ∑ i, (B.dim i : ℂ) ^ (2 - 2 * (g : ℤ)) =
      (Fintype.card G : ℂ) ^ (1 - 2 * (g : ℤ)) * Nat.card (SurfaceGroup g →* G) := by sorry

end FrobMednykh
