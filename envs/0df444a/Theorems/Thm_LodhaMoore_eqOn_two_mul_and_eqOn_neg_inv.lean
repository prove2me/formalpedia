-- Prove2me | Theorems.Thm_LodhaMoore_eqOn_two_mul_and_eqOn_neg_inv
-- name    : LodhaMoore.eqOn_two_mul_and_eqOn_neg_inv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T05:58:05.672154+00:00
-- url     : https://prove2.me/theorems/c339d893-8531-4068-b329-b3002e05891d
-- title:
--   §2 — bca⁻¹c⁻¹a is t ↦ 2t on [0, 1], and aba and ba⁻³ are t ↦ −1/t on [−1, −1/2] and [1/2, 1]
-- statement:
--   With products taken left to right, as in the paper: the element $bca^{-1}c^{-1}a$ maps $t$ to $2t$ for $t \in [0, 1]$; $aba$ maps $t$ to $-1/t$ for $t \in [-1, -1/2]$; and $ba^{-3}$ maps $t$ to $-1/t$ for $t \in [1/2, 1]$.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 4, §2

import Mathlib
import Definitions.Def_LodhaMoore

namespace LodhaMoore

theorem eqOn_two_mul_and_eqOn_neg_inv :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      MulOpposite.unop (MulOpposite.op b * MulOpposite.op c * (MulOpposite.op a)⁻¹ * (MulOpposite.op c)⁻¹ * MulOpposite.op a) (t : OnePoint ℝ) = ((2 * t : ℝ) : OnePoint ℝ)) ∧
    (∀ t ∈ Set.Icc (-1 : ℝ) (-1 / 2),
      MulOpposite.unop (MulOpposite.op a * MulOpposite.op b * MulOpposite.op a) (t : OnePoint ℝ) = ((-1 / t : ℝ) : OnePoint ℝ)) ∧
    (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      MulOpposite.unop (MulOpposite.op b * (MulOpposite.op a)⁻¹ ^ (3 : ℕ) : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) (t : OnePoint ℝ) = ((-1 / t : ℝ) : OnePoint ℝ)) := by
  sorry

end LodhaMoore
