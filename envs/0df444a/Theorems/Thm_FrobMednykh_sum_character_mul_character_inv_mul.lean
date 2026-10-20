-- Prove2me | Theorems.Thm_FrobMednykh_sum_character_mul_character_inv_mul
-- name    : FrobMednykh.sum_character_mul_character_inv_mul
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-19T19:15:37.632956+00:00
-- url     : https://prove2.me/theorems/02e47c5a-1689-4f10-a2a2-8e7e51046e85
-- title:
--   Convolution orthogonality of irreducible characters
-- statement:
--   For irreducible $V,W$ and $z\in G$: $\sum_{x\in G}\chi_V(x)\chi_W(x^{-1}z)$ equals $\frac{|G|}{d_V}\chi_V(z)$ if $V\cong W$, and $0$ otherwise.
-- source:
--   M. Mulase, J. T. Yu, A generating function of the number of homomorphisms from a surface group into a finite group, arXiv:math/0209008 (2002), https://arxiv.org/abs/math/0209008, §4 eq. (4.2): χ_λ ⋆ χ_μ = δ_{λμ} |G|/dim V_λ · χ_λ

import Definitions.Def_FrobMednykh_defs

open CategoryTheory

namespace FrobMednykh

open Classical in
theorem sum_character_mul_character_inv_mul {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G) [Simple V] [Simple W] (z : G) :
    ∑ x : G, V.character x * W.character (x⁻¹ * z) =
      if Nonempty (V ≅ W) then (Fintype.card G : ℂ) / Module.finrank ℂ V * V.character z
      else 0 := by sorry

end FrobMednykh
