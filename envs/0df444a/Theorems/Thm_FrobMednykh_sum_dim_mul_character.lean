-- Prove2me | Theorems.Thm_FrobMednykh_sum_dim_mul_character
-- name    : FrobMednykh.sum_dim_mul_character
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-19T19:14:59.08528+00:00
-- url     : https://prove2.me/theorems/ca317efe-fdbb-4d2f-8598-f70c1bd56ddd
-- title:
--   Column orthogonality at the identity
-- statement:
--   $G$ is a finite group; representations are finite-dimensional over $\mathbb C$ (`FDRep ℂ G`), $\chi_V$ is the character and $d_V=\dim V$. An `IrrepFamily G ι` is a family $(V_i)_{i\in\iota}$ of irreducible representations, pairwise non-isomorphic, such that every irreducible representation is isomorphic to some $V_i$; $d_i=\dim V_i$, $\chi_i=\chi_{V_i}$. For every $z\in G$: $\sum_i d_i\,\chi_i(z)=|G|$ if $z=1$, and $0$ otherwise.
-- source:
--   M. Mulase, J. T. Yu, A generating function of the number of homomorphisms from a surface group into a finite group, arXiv:math/0209008 (2002), https://arxiv.org/abs/math/0209008, Remark 1.2 and §4 (orthogonality of irreducible characters); J.-P. Serre, Linear Representations of Finite Groups (Springer GTM 42, 1977), §2.4 Corollary 2

import Definitions.Def_FrobMednykh_defs

open CategoryTheory

namespace FrobMednykh

theorem sum_dim_mul_character {G ι : Type} [Group G] [Fintype G] [DecidableEq G] [Fintype ι]
    (B : IrrepFamily G ι) (z : G) :
    ∑ i, (B.dim i : ℂ) * (B.V i).character z = if z = 1 then (Fintype.card G : ℂ) else 0 := by sorry

end FrobMednykh
