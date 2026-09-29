-- Prove2me | Theorems.Thm_LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one
-- name    : LanglandsTunnell.Artin.eq_one_or_eq_commutator_of_det_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/2dac7ff2-fe35-52a1-b03f-7f430106afa4
-- title:
--   Determinant one in GL₂(𝔽₃): identity or commutator
-- statement:
--   The assertion is a statement about the group $\mathrm{GL}_2(\mathbb{Z}/3)$ of units of the ring of $2 \times 2$ matrices over $\mathbb{Z}/3\mathbb{Z}$. For every $g \in \mathrm{GL}_2(\mathbb{Z}/3)$ whose underlying matrix has determinant equal to $1$, one of the following holds: either the underlying matrix of $g$ is the identity matrix, or there exist $x, y \in \mathrm{GL}_2(\mathbb{Z}/3)$ such that $g = x y x^{-1} y^{-1}$, this last equality being an equality in the group of units (the first alternative, by contrast, is stated as an equality of matrices). Thus every element of determinant $1$ is either trivial or a single commutator of two elements of the full general linear group; no claim is made that $x$ and $y$ may be taken of determinant $1$. Since a commutator always has determinant $1$, the statement identifies the derived subgroup of $\mathrm{GL}_2(\mathbb{F}_3)$ with $\mathrm{SL}_2(\mathbb{F}_3)$, and exhibits it as consisting of single commutators.
--
--   This is the elementary group-theoretic input that the abelianisation of $\mathrm{GL}_2(\mathbb{F}_3)$ is detected by the determinant, in the sharp form that each element of $\mathrm{SL}_2(\mathbb{F}_3)$ is a single commutator. It is used in the Langlands–Tunnell part of the development, where [`LanglandsTunnell.P2.raySymbol_artinValue_span_eq_one`](thm.html#LanglandsTunnell.P2.raySymbol_artinValue_span_eq_one) needs that a character-type quantity attached to an element of determinant one is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one.lean

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.Artin.eq_one_or_eq_commutator_of_det_eq_one :
    ∀ g : GL (Fin 2) (ZMod 3), (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 →
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 ∨
        ∃ x : GL (Fin 2) (ZMod 3), ∃ y : GL (Fin 2) (ZMod 3), g = x * y * x⁻¹ * y⁻¹ := by sorry
