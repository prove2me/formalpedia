-- Prove2me | Theorems.Thm_LT_LatticeTree_unitOrbitalCount_eq_one_of_anisotropic_and_eq_two_of_eisenstein_of_depth_zero
-- name    : LT.LatticeTree.unitOrbitalCount_eq_one_of_anisotropic_and_eq_two_of_eisenstein_of_depth_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/e964d74f-d260-5fa3-bd65-43fa9df9d0b0
-- title:
--   Fixed vertices at depth zero: one in the anisotropic case, two in the Eisenstein case
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain, integral and discretely valued) with field of fractions $K$, let $\varpi \in R$ be an irreducible element, and assume the residue ring $R/(\varpi)$ is finite. For an invertible matrix $g \in \mathrm{GL}_2(K)$, write $\mathrm{LT.LatticeTree.unitOrbitalCount}\ R\ g$ for the number of vertices of `Vertex R K` fixed by $g$, that is `Nat.card` of the set of $v$ satisfying `IsFixedVertex g v`. The theorem asserts two statements simultaneously. First: for every $Y \in M_2(R)$, every $b \in R$ and every $g \in \mathrm{GL}_2(K)$, if the reduction of $Y$ modulo $\varpi$ has no nonzero eigenvector over $R/(\varpi)$ — for all $a \in R/(\varpi)$ and all $w \in (R/(\varpi))^2$ with $(Y \bmod \varpi)\, w = a w$ one has $w = 0$ — and if $\det(b \cdot 1 + Y)$ is a unit of $R$, and if the matrix of $g$ over $K$ is the image of $b \cdot 1 + Y$ under $R \to K$, then $g$ fixes exactly one vertex. Second: for every $Y \in M_2(R)$, every unit $w \in R^\times$, every $b \in R$ and every $g \in \mathrm{GL}_2(K)$, if $\det Y = \varpi w$, if $\varpi$ divides $\operatorname{tr} Y$, if $\det(b \cdot 1 + Y)$ is a unit, and if the matrix of $g$ over $K$ is the image of $b \cdot 1 + Y$, then $g$ fixes exactly two vertices.
--
--   This is the depth-zero case of the count of vertices of the Bruhat–Tits tree of $\mathrm{GL}_2(K)$ fixed by an element whose characteristic polynomial generates an unramified, respectively ramified (Eisenstein), quadratic extension of $K$: one fixed vertex in the anisotropic case, two (adjacent) ones in the Eisenstein case. It serves as the base case for [`LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth`](thm.html#LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth), where the counts at higher depth are obtained by a recursion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_unitOrbitalCount_eq_one_of_anisotropic_and_eq_two_of_eisenstein_of_depth_zero.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Matrix

theorem LT.LatticeTree.unitOrbitalCount_eq_one_of_anisotropic_and_eq_two_of_eisenstein_of_depth_zero
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] :
    (∀ (Y : Matrix (Fin 2) (Fin 2) R) (b : R) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      (∀ (a : R ⧸ Ideal.span {ϖ}) (w : Fin 2 → R ⧸ Ideal.span {ϖ}),
        (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0) →
      IsUnit (b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).det →
      (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K b • 1 + Y.map (algebraMap R K) →
      LT.LatticeTree.unitOrbitalCount R g = 1) ∧
    (∀ (Y : Matrix (Fin 2) (Fin 2) R) (w : Rˣ) (b : R) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      Y.det = ϖ * (w : R) → ϖ ∣ Y.trace →
      IsUnit (b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).det →
      (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K b • 1 + Y.map (algebraMap R K) →
      LT.LatticeTree.unitOrbitalCount R g = 2) := by sorry
