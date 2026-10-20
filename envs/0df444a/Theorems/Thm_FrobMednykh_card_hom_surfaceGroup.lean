-- Prove2me | Theorems.Thm_FrobMednykh_card_hom_surfaceGroup
-- name    : FrobMednykh.card_hom_surfaceGroup
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-19T19:14:46.525003+00:00
-- url     : https://prove2.me/theorems/d1d45625-157c-4bcf-954b-3b3f03d8e854
-- title:
--   Homomorphisms from the surface group are commutator tuples
-- statement:
--   $\Gamma_g$ (`SurfaceGroup g`) is the presented group $\langle a_1,b_1,\dots,a_g,b_g\mid [a_1,b_1]\cdots[a_g,b_g]\rangle$, the standard presentation of $\pi_1$ of the closed orientable genus-$g$ surface. $N_g(z)$ (`commCount G g z`) is the number of $((x_1,y_1),\dots,(x_g,y_g))\in(G\times G)^g$ with $[x_1,y_1]\cdots[x_g,y_g]=z$, where $[x,y]=xyx^{-1}y^{-1}$. For finite $G$: $\#\mathrm{Hom}(\Gamma_g,G)=N_g(1)$.
-- source:
--   M. Mulase, J. T. Yu, A generating function of the number of homomorphisms from a surface group into a finite group, arXiv:math/0209008 (2002), https://arxiv.org/abs/math/0209008, §4, last paragraph of the proof of Thm. 4.1 (f_g(1) = |Hom(π₁(S), G)|); N. Snyder, Mednykh's formula via lattice topological quantum field theories, arXiv:math/0703073 (2007), https://arxiv.org/abs/math/0703073, eq. (1)

import Definitions.Def_FrobMednykh_defs

open CategoryTheory

namespace FrobMednykh

theorem card_hom_surfaceGroup (G : Type) [Group G] [Finite G] (g : ℕ) :
    Nat.card (SurfaceGroup g →* G) = commCount G g 1 := by sorry

end FrobMednykh
