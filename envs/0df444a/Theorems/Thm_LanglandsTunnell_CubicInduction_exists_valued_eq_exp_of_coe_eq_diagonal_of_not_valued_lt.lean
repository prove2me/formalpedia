-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt
-- name    : LanglandsTunnell.CubicInduction.exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b7370093-a0e8-5a8e-923c-d23c3c01e529
-- title:
--   Valuation exponents of a dominant diagonal element of GL₃
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, i.e. a finite place, and let $\mathbb{Q}_v$ denote the $v$-adic completion of $\mathbb{Q}$, with its valuation $\mathrm{Valued.v}$ taking values in $\mathbb{Z}$ adjoined $0$ written multiplicatively (so $\mathrm{WithZero.exp}$ sends an integer $n$ to the corresponding nonzero value). Let $t$ be an element of `LocalGL3 v`, the general linear group $\mathrm{GL}_3(\mathbb{Q}_v)$, and let $d : \mathrm{Fin}\,3 \to \mathbb{Q}_v$ be a triple of scalars. Assume that the underlying $3\times 3$ matrix of $t$ is the diagonal matrix with entries $d_0, d_1, d_2$, and assume the dominance condition that neither $v(d_1) < v(d_0)$ nor $v(d_2) < v(d_1)$ holds. The conclusion asserts the existence of natural numbers $k_1, k_2$ and an integer $c$ with $v(d_0) = \mathrm{exp}(-(k_1 + c))$, $v(d_1) = \mathrm{exp}(-(k_2 + c))$ and $v(d_2) = \mathrm{exp}(-c)$; thus the three valuations are decreasing in the exponent sense, with the last exponent $c$ arbitrary in $\mathbb{Z}$ and the first two exceeding it by non-negative amounts.
--
--   This is the normalisation of a dominant diagonal element of $\mathrm{GL}_3$ over a local field into the form $\mathrm{diag}(\pi^{-(k_1+c)}, \pi^{-(k_2+c)}, \pi^{-c})$ with $k_1, k_2 \ge 0$, the shape in which Hecke operators and Whittaker functions at a finite place are indexed. It is used in the analysis of spherical and Whittaker data at good places, in the construction of induced spherical vectors and in the proof of multiplicity one for Whittaker functionals of coset eigenfunctions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt
    (v : HeightOneSpectrum (𝓞 ℚ)) (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (hd : ¬ (Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1))) :
    ∃ (k₁ k₂ : ℕ) (c : ℤ), Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)) ∧
      Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)) ∧ Valued.v (d 2) = WithZero.exp (-c) := by sorry
