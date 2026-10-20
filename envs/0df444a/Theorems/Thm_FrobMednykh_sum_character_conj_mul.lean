-- Prove2me | Theorems.Thm_FrobMednykh_sum_character_conj_mul
-- name    : FrobMednykh.sum_character_conj_mul
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-19T19:15:20.035165+00:00
-- url     : https://prove2.me/theorems/6dfbe4f1-842c-427c-9ce1-fb938f615c44
-- title:
--   Class sums act by scalars (Schur)
-- statement:
--   For an irreducible $V$ of dimension $d$ and $x,y\in G$: $\sum_{a\in G}\chi_V(axa^{-1}y)=\frac{|G|}{d}\,\chi_V(x)\,\chi_V(y)$.
-- source:
--   M. Mulase, J. T. Yu, A generating function of the number of homomorphisms from a surface group into a finite group, arXiv:math/0209008 (2002), https://arxiv.org/abs/math/0209008, §4 (projections pr_λ of Z C[G], used for the f_1 formula); J.-P. Serre, Linear Representations of Finite Groups (Springer GTM 42, 1977), §2.5 (proof of Prop. 6)

import Definitions.Def_FrobMednykh_defs

open CategoryTheory

namespace FrobMednykh

theorem sum_character_conj_mul {G : Type} [Group G] [Fintype G] (V : FDRep ℂ G) [Simple V]
    (x y : G) :
    ∑ a : G, V.character (a * x * a⁻¹ * y) =
      (Fintype.card G : ℂ) / Module.finrank ℂ V * V.character x * V.character y := by sorry

end FrobMednykh
