-- Prove2me | Theorems.Thm_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice
-- name    : LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/c468f4cc-e060-545b-ab7c-b78940970adb
-- title:
--   Upper-triangular normal form for full lattices in K²
-- statement:
--   Let $R$ be a commutative domain that is a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure making it a field of fractions of $R$; let $\varpi \in R$ be irreducible, and let $L$ be an $R$-submodule of $K^2$ (functions on `Fin 2`) which is a full lattice, meaning that $L$ is finitely generated as an $R$-module and that its $K$-span inside $K^2$ is everything. The assertion is that there exist a unit $c \in K^\times$, an integer $n$, an element $\beta \in K$ and an element $g$ of $\mathrm{GL}_2(K)$ such that the underlying matrix of $g$ is $\begin{pmatrix} \varpi^{n} & \beta \\ 0 & 1\end{pmatrix}$, with $\varpi$ read in $K$ through the algebra map and the integer power taken in $K$, and such that $L$ is the image of the standard lattice under the linear map $v \mapsto (c\cdot 1 \cdot g)\,v$, where $c \cdot 1$ denotes the scalar matrix with diagonal entries $c$ viewed in $\mathrm{GL}_2(K)$. Here the standard lattice is the set of vectors in $K^2$ both of whose coordinates lie in the image of $R$ in $K$. No uniqueness of $c$, $n$, $\beta$ or $g$ is claimed.
--
--   This is the Iwasawa decomposition $\mathrm{GL}_2(K) = B(K)\,\mathrm{GL}_2(R)$ read on lattices, equivalently Hermite normal form for a basis matrix over a discrete valuation ring; the pair $(n,\beta)$ is the standard apartment chart for the vertices of the Bruhat–Tits tree of $\mathrm{GL}_2(K)$. It is used in the construction of lattice chains and edge charts for the Čerednik–Drinfeld moduli data, in particular in the comparison of full lattices with the standard one and in the admissibility statements for the associated group action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice.lean

import Definitions.Def_LatticeTreeOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LT.LatticeTree

theorem LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    ∃ (c : Kˣ) (n : ℤ) (β : K) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      (g : Matrix (Fin 2) (Fin 2) K) = !![algebraMap R K ϖ ^ n, β; 0, 1] ∧
      L = latticeMap (scalarGL c * g) (stdLattice R K) := by sorry
