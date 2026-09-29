-- Prove2me | Theorems.Thm_LT_LatticeTree_unitOrbitalCount_ne_zero_of_anisotropic
-- name    : LT.LatticeTree.unitOrbitalCount_ne_zero_of_anisotropic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/c4879b5f-706e-563c-9a68-d03fcf9e1d10
-- title:
--   Non-vanishing unit orbital count for anisotropic classes
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, with fraction field $K$, let $\varpi \in R$ be irreducible and suppose the residue ring $R/(\varpi)$ is finite. Let $d$ be a natural number, $\gamma$ an element of $\mathrm{GL}_2(R)$, $mu$ a unit of $R$ and $Y$ a $2\times 2$ matrix over $R$ such that entrywise $\gamma_{ij} = mu \cdot \delta_{ij} + \varpi^{d} Y_{ij}$, that is, $\gamma = mu\cdot 1 + \varpi^{d} Y$. Assume moreover that the reduction of $Y$ modulo $\varpi$ is anisotropic in the sense that for every scalar $a$ in $R/(\varpi)$ and every vector $v \in (R/(\varpi))^{2}$, the equality $\overline{Y} v = a v$ forces $v = 0$; equivalently, $\overline{Y}$ has no eigenvector over the residue field. Then, writing $g$ for the image of $\gamma$ in $\mathrm{GL}_2(K)$ under the map induced by $R \to K$, the quantity [`LT.LatticeTree.unitOrbitalCount R g`](def/LatticeTreeOrbital.html#L1442), defined as the `Nat.card` of the set of those $v$ in `Vertex R K` with `IsFixedVertex g v`, is non-zero. Since `Nat.card` vanishes on infinite sets, the assertion is that this fixed set is finite and non-empty; no closed formula for its cardinality is claimed.
--
--   The statement records that a class of the above shape — a unit scalar plus $\varpi^{d}$ times a matrix with anisotropic reduction — has a finite, non-empty fixed-point set on the tree of lattices, so that its vertex count is a genuine positive integer rather than the conventional value $0$ attached to infinite sets. It is used in the comparison of orbital and twisted orbital integrals with their tree-theoretic counts and in the construction of matching local Hecke operators at an inert prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_unitOrbitalCount_ne_zero_of_anisotropic.lean

import Definitions.Def_LatticeTreeOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Matrix

theorem LT.LatticeTree.unitOrbitalCount_ne_zero_of_anisotropic
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (d : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j,
      (γ : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (hanis : ∀ (a : R ⧸ Ideal.span {ϖ}) (v : Fin 2 → R ⧸ Ideal.span {ϖ}),
      (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})) *ᵥ v = a • v → v = 0) :
    LT.LatticeTree.unitOrbitalCount R (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) ≠ 0 := by sorry
