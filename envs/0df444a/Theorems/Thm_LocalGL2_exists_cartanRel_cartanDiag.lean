-- Prove2me | Theorems.Thm_LocalGL2_exists_cartanRel_cartanDiag
-- name    : LocalGL2.exists_cartanRel_cartanDiag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/1b78e505-9703-5627-ae99-db7afbdd410a
-- title:
--   Existence of a Cartan representative for 2× 2 matrices over a DVR
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, let $\varpi \in R$ be irreducible, and let $g$ be a $2\times 2$ matrix over $R$ (indexed by `Fin 2`) whose determinant is non-zero. Then there exist natural numbers $a \le b$ such that $g$ and the diagonal matrix `cartanDiag` $\varpi\,a\,b = \mathrm{diag}(\varpi^a, \varpi^b)$ are related by `CartanRel`, i.e. there are units $k_1, k_2$ of the matrix ring $M_2(R)$ — equivalently elements of $\mathrm{GL}_2(R)$ — with $g = k_1 \cdot \mathrm{diag}(\varpi^a,\varpi^b) \cdot k_2$. Note that the exponents are natural numbers, so this is the integral statement for matrices with entries in $R$; only existence of such a triple $(a,b,k_1,k_2)$ is asserted, with no uniqueness claim, and the ordering $a \le b$ is part of the conclusion.
--
--   This is the existence half of the integral Cartan decomposition (elementary divisor form of Smith normal form) for $\mathrm{GL}_2$ over a discrete valuation ring, which organises the double cosets $\mathrm{GL}_2(R)\,\mathrm{diag}(\varpi^a,\varpi^b)\,\mathrm{GL}_2(R)$. It underlies the local theory of $\mathrm{GL}_2$ in the project: it is used in the computation of distances between standard vertices of the Bruhat–Tits tree, in the construction of the local Hecke algebra homomorphisms attached to Cartan double cosets, and in the uniqueness statement for representatives of such double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_exists_cartanRel_cartanDiag.lean

import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Matrix LocalGL2

theorem LocalGL2.exists_cartanRel_cartanDiag
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    (g : Matrix (Fin 2) (Fin 2) R) (hg : g.det ≠ 0) :
    ∃ a b : ℕ, a ≤ b ∧ CartanRel g (cartanDiag ϖ a b) := by sorry
