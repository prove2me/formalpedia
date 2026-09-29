-- Prove2me | Theorems.Thm_LT_LatticeTree_unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth
-- name    : LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/a2591e9d-5ff4-5713-8ad2-f506227e7298
-- title:
--   Fixed-vertex counts for a+varpi^m Y: two kinds
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, $K$ a field that is an $R$-algebra and a fraction field of $R$, $\varpi\in R$ irreducible, and suppose the residue ring $R/(\varpi)$ is finite; write $q=$ `Nat.card` $(R/(\varpi))$. For $g\in GL_2(K)$, [`LT.LatticeTree.unitOrbitalCount R g`](def/LatticeTreeOrbital.html#L1442) is the cardinality (`Nat.card`) of the set of vertices of [`LT.LatticeTree.Vertex R K`](def/LatticeTreeOrbital.html#L349) satisfying `IsFixedVertex g`. The assertion is a conjunction of two statements. First (anisotropic kind): for every $Y\in M_2(R)$ whose reduction modulo $\varpi$ has no eigenvector, i.e. for all $a\in R/(\varpi)$ and $w\in (R/(\varpi))^2$ with $\bar Y w=a\,w$ one has $w=0$, and for all $m\in\mathbb N$, $a\in R$ and $g\in GL_2(K)$ whose underlying matrix equals $a\cdot 1+\varpi^m\,Y$ (images taken under $R\to K$) and such that $\det(a\cdot 1+\varpi^m Y)$ is a unit of $R$, one has $(q-1)\cdot$ `unitOrbitalCount R g` $+\,2=(q+1)q^m$. Second (Eisenstein kind): the same conclusion with right-hand side $2q^{m+1}$ holds for every $Y\in M_2(R)$ such that $\det Y=\varpi u$ for some $u\in R^\times$ and $\varpi\mid \operatorname{tr} Y$, under the same hypotheses on $m,a,g$. Both equalities are in $\mathbb N$, so $q-1$ is truncated subtraction.
--
--   This is the count of vertices of the Bruhat–Tits tree of $GL_2$ fixed by an integral element $a+\varpi^m Y$ with unit determinant: a ball of radius $m$ in the anisotropic case, giving $1+(q+1)(q^m-1)/(q-1)$ vertices, and a tube of radius $m$ about an edge in the Eisenstein case, giving $2(q^{m+1}-1)/(q-1)$. It feeds the evaluation of orbital integrals of indicator functions of scalars times a principal congruence subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth.lean

import Definitions.Def_LatticeTreeBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Matrix

theorem LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] :
    (∀ (Y : Matrix (Fin 2) (Fin 2) R),
      (∀ (a : R ⧸ Ideal.span {ϖ}) (w : Fin 2 → R ⧸ Ideal.span {ϖ}),
        (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0) →
      ∀ (m : ℕ) (a : R) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K a • 1 + algebraMap R K ϖ ^ m • Y.map (algebraMap R K) →
      IsUnit (a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ m • Y).det →
      (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) * LT.LatticeTree.unitOrbitalCount R g + 2 =
        (Nat.card (R ⧸ Ideal.span {ϖ}) + 1) * Nat.card (R ⧸ Ideal.span {ϖ}) ^ m) ∧
    (∀ (Y : Matrix (Fin 2) (Fin 2) R) (w : Rˣ), Y.det = ϖ * (w : R) → ϖ ∣ Y.trace →
      ∀ (m : ℕ) (a : R) (g : Matrix.GeneralLinearGroup (Fin 2) K),
      (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K a • 1 + algebraMap R K ϖ ^ m • Y.map (algebraMap R K) →
      IsUnit (a • (1 : Matrix (Fin 2) (Fin 2) R) + ϖ ^ m • Y).det →
      (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) * LT.LatticeTree.unitOrbitalCount R g + 2 =
        2 * Nat.card (R ⧸ Ideal.span {ϖ}) ^ (m + 1)) := by sorry
