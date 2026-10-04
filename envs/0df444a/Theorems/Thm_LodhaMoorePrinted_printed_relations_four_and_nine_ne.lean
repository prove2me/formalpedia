-- Prove2me | Theorems.Thm_LodhaMoorePrinted_printed_relations_four_and_nine_ne
-- name    : LodhaMoorePrinted.printed_relations_four_and_nine_ne
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T19:30:39.574975+00:00
-- url     : https://prove2.me/theorems/b8f729b4-c077-4b08-91bc-5999cf6f5e71
-- title:
--   Lodha–Moore p. 7 — the printed fourth and ninth relations of G₀ do not hold
-- statement:
--   In Lodha and Moore's group $G_0 = \langle a, b, c \rangle$ of homeomorphisms of the projective line (p. 2; products are composed left to right, so the statement is written in the opposite group), two of the nine relations printed on p. 7 fail:
--   $$c\,b^2a^{-1}bab \ne b^2a^{-1}bab\,c,$$
--   and $c$ is not equal to $b^2a^{-1}b^{-1}acb^{-2}ab^{-1}c^{-1}ba^{-1}bab^{-1}ab^{-1}cba^{-1}ba^{-1}$.
--
--   On p. 7 these are the fourth relation "$cb^2a^{-1}bab = b^2a^{-1}babc$" and the ninth relation "$c = b^2a^{-1}b^{-1}acb^{-2}ab^{-1}c^{-1}ba^{-1}bab^{-1}ab^{-1}cba^{-1}ba^{-1}$". The paper obtains them by expressing the relations $y_{10}x_{01} = x_{01}y_{10}$ and $y_{10} = x_{10}y_{100}y_{1010}^{-1}y_{1011}$ in terms of $a$, $b$ and $c$. Those relations hold, and the Lodha–Moore mission's list of relations (`LodhaMoore.nineRels`) uses their translations through the definitions of p. 6. In each relation, the two sides act differently at, for instance, $t = 29/390$.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 7, the list of nine relations for G_0

import Definitions.Def_LodhaMoore
import Mathlib

namespace LodhaMoorePrinted

theorem printed_relations_four_and_nine_ne :
    (MulOpposite.op LodhaMoore.c : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) * MulOpposite.op LodhaMoore.b ^ (2 : ℕ) * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.a * MulOpposite.op LodhaMoore.b ≠
      (MulOpposite.op LodhaMoore.b ^ (2 : ℕ) : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.a * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.c ∧
    (MulOpposite.op LodhaMoore.c : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) ≠
      (MulOpposite.op LodhaMoore.b ^ (2 : ℕ) : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) * (MulOpposite.op LodhaMoore.a)⁻¹ * (MulOpposite.op LodhaMoore.b)⁻¹ * MulOpposite.op LodhaMoore.a * MulOpposite.op LodhaMoore.c * (MulOpposite.op LodhaMoore.b)⁻¹ ^ (2 : ℕ) * MulOpposite.op LodhaMoore.a * (MulOpposite.op LodhaMoore.b)⁻¹ * (MulOpposite.op LodhaMoore.c)⁻¹ * MulOpposite.op LodhaMoore.b * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.a * (MulOpposite.op LodhaMoore.b)⁻¹ * MulOpposite.op LodhaMoore.a * (MulOpposite.op LodhaMoore.b)⁻¹ * MulOpposite.op LodhaMoore.c * MulOpposite.op LodhaMoore.b * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * (MulOpposite.op LodhaMoore.a)⁻¹ := by
  sorry

end LodhaMoorePrinted
