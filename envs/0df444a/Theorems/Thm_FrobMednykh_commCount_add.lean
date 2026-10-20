-- Prove2me | Theorems.Thm_FrobMednykh_commCount_add
-- name    : FrobMednykh.commCount_add
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-19T19:16:05.368039+00:00
-- url     : https://prove2.me/theorems/3fc1993c-f7e8-43b5-8f26-2773ab75df01
-- title:
--   Commutator counts convolve: f_{g₁+g₂} = f_{g₁} ⋆ f_{g₂}
-- statement:
--   $N_g(z)$ (`commCount G g z`) is the number of $((x_1,y_1),\dots,(x_g,y_g))\in(G\times G)^g$ with $[x_1,y_1]\cdots[x_g,y_g]=z$, where $[x,y]=xyx^{-1}y^{-1}$. For finite $G$, all $g_1,g_2\ge0$ and $w\in G$: $N_{g_1+g_2}(w)=\sum_{\sigma\in G}N_{g_1}(w\sigma^{-1})\,N_{g_2}(\sigma)$.
-- source:
--   M. Mulase, J. T. Yu, A generating function of the number of homomorphisms from a surface group into a finite group, arXiv:math/0209008 (2002), https://arxiv.org/abs/math/0209008, §4, proof of Theorem 4.1 (f_{g1+g2} = f_{g1} ⋆ f_{g2})

import Definitions.Def_FrobMednykh_defs

open CategoryTheory

namespace FrobMednykh

theorem commCount_add (G : Type) [Group G] [Fintype G] (g₁ g₂ : ℕ) (w : G) :
    commCount G (g₁ + g₂) w = ∑ σ : G, commCount G g₁ (w * σ⁻¹) * commCount G g₂ σ := by sorry

end FrobMednykh
