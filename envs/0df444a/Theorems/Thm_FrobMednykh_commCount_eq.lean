-- Prove2me | Theorems.Thm_FrobMednykh_commCount_eq
-- name    : FrobMednykh.commCount_eq
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-19T19:16:18.640263+00:00
-- url     : https://prove2.me/theorems/2db5c79f-d194-49ad-9cf2-92019fdec1dd
-- title:
--   Number of genus-g commutator tuples with prescribed product
-- statement:
--   $G$ is a finite group; representations are finite-dimensional over $\mathbb C$ (`FDRep ℂ G`), $\chi_V$ is the character and $d_V=\dim V$. An `IrrepFamily G ι` is a family $(V_i)_{i\in\iota}$ of irreducible representations, pairwise non-isomorphic, such that every irreducible representation is isomorphic to some $V_i$; $d_i=\dim V_i$, $\chi_i=\chi_{V_i}$. $N_g(z)$ (`commCount G g z`) is the number of $((x_1,y_1),\dots,(x_g,y_g))\in(G\times G)^g$ with $[x_1,y_1]\cdots[x_g,y_g]=z$, where $[x,y]=xyx^{-1}y^{-1}$. For all $g\ge0$ and $z\in G$: $N_g(z)=|G|^{2g-1}\sum_i\chi_i(z)\,d_i^{\,1-2g}$ (integer powers in $\mathbb C$).
-- source:
--   M. Mulase, J. T. Yu, A generating function of the number of homomorphisms from a surface group into a finite group, arXiv:math/0209008 (2002), https://arxiv.org/abs/math/0209008, §4 Theorem 4.1, eq. (4.4) (stated for g ≥ 1; g = 0 included here)

import Definitions.Def_FrobMednykh_defs

open CategoryTheory

namespace FrobMednykh

theorem commCount_eq {G ι : Type} [Group G] [Fintype G] [Fintype ι]
    (B : IrrepFamily G ι) (g : ℕ) (z : G) :
    (commCount G g z : ℂ) =
      (Fintype.card G : ℂ) ^ (2 * (g : ℤ) - 1) *
        ∑ i, (B.V i).character z * (B.dim i : ℂ) ^ (1 - 2 * (g : ℤ)) := by sorry

end FrobMednykh
