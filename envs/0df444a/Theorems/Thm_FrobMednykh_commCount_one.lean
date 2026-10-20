-- Prove2me | Theorems.Thm_FrobMednykh_commCount_one
-- name    : FrobMednykh.commCount_one
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-19T19:15:53.764101+00:00
-- url     : https://prove2.me/theorems/6076e3c4-e715-407a-9ad2-75ecd74bfbb2
-- title:
--   Frobenius' commutator count (genus one)
-- statement:
--   $G$ is a finite group; representations are finite-dimensional over $\mathbb C$ (`FDRep ℂ G`), $\chi_V$ is the character and $d_V=\dim V$. An `IrrepFamily G ι` is a family $(V_i)_{i\in\iota}$ of irreducible representations, pairwise non-isomorphic, such that every irreducible representation is isomorphic to some $V_i$; $d_i=\dim V_i$, $\chi_i=\chi_{V_i}$. $N_g(z)$ (`commCount G g z`) is the number of $((x_1,y_1),\dots,(x_g,y_g))\in(G\times G)^g$ with $[x_1,y_1]\cdots[x_g,y_g]=z$, where $[x,y]=xyx^{-1}y^{-1}$. For every $z\in G$: $N_1(z)=|G|\sum_i\chi_i(z)/d_i$.
-- source:
--   M. Mulase, J. T. Yu, A generating function of the number of homomorphisms from a surface group into a finite group, arXiv:math/0209008 (2002), https://arxiv.org/abs/math/0209008, §4, the formula for f_1 used in the proof of Thm. 4.1 (cited there to Stanley); G. Frobenius, Über Gruppencharaktere (1896)

import Definitions.Def_FrobMednykh_defs

open CategoryTheory

namespace FrobMednykh

theorem commCount_one {G ι : Type} [Group G] [Fintype G] [Fintype ι]
    (B : IrrepFamily G ι) (z : G) :
    (commCount G 1 z : ℂ) = Fintype.card G * ∑ i, (B.V i).character z / B.dim i := by sorry

end FrobMednykh
