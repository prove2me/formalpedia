-- Prove2me | Theorems.Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
-- name    : LT.LatticeTree.card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/64862fd6-338d-587c-bb55-23b67b8b7140
-- title:
--   Counting vertices at twisted distance exactly n by double cosets
-- statement:
--   Let $R$ be a discrete valuation ring that is a domain, with fraction field $K$, let $\sigma$ be an `IntegralAut R K`, that is a pair consisting of a ring automorphism of $K$ and one of $R$ compatible with the structure map, and write $\sigma$ also for the induced automorphism of $\mathrm{GL}_2(K)$ acting entrywise (`σ.mapGL`). Let $\varpi \in R$ be irreducible with finite residue ring $R/(\varpi)$ and fixed by the automorphism of $R$ underlying $\sigma$. Let $\delta \in \mathrm{GL}_2(K)$, $b \in \mathbb{Z}$, $n \geq 1$ a natural number and $u \in R^{\times}$ with $\det \delta = u\varpi^{2b+n}$ in $K$, and let $dl \in \mathrm{GL}_2(K)$ have underlying matrix $\mathrm{diag}(\varpi^{b+n}, \varpi^{b})$. Write $T$ for the $\sigma$-twisted centraliser $\{t : t\delta\sigma(t)^{-1} = \delta\}$ of $\delta$ and $U$ for the set of $g \in \mathrm{GL}_2(K)$ such that both $g$ and $g^{-1}$ have all entries in the image of $R$. Assume given a subgroup $T_c$ whose elements are exactly the $t \in T$ with $\det t$ the image of a unit of $R$, and for each $s$ a subgroup $T_s$ whose elements are exactly the $t \in T$ with $s^{-1}ts \in U$. Let $S$ be a finite set of elements $s$ with $s^{-1}\delta\sigma(s) \in U\,dl\,U$, pairwise inequivalent in the sense that $s' = tsv$ with $s,s' \in S$, $t \in T$, $v \in U$ forces $s' = s$, and such that every $x \in \mathrm{GL}_2(K)$ with $x^{-1}\delta\sigma(x) \in U\,dl\,U$ can be written $x = tsv$ with $s \in S$, $t \in T$, $v \in U$. Then the number of vertices $x$ of the tree of $K$ (homothety classes of full $R$-lattices in $K^2$) lying in the ball of radius $n$, for the scale given by the unit $\varpi$ of $K$, about their image under the twisted action $x \mapsto \delta \cdot \sigma(x)$ but not in the corresponding ball of radius $n-1$, equals the index of $(T_c \vee Z) \cap T$ in $T$, with $Z$ the centre of $\mathrm{GL}_2(K)$, multiplied by $\sum_{s \in S}$ of the index of $T_s \cap T_c$ in $T_c$.
--
--   This is the local combinatorial count underlying the evaluation of twisted orbital integrals on $\mathrm{GL}_2$ over a local field: the vertices moved to twisted distance exactly $n$ are parametrised by the twisted double cosets $T\backslash\{x : x^{-1}\delta\sigma(x) \in U\,dl\,U\}/U$, each contributing a ratio of group indices. It is used in the untwisted analogue [`LT.LatticeTree.card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow`](thm.html#LT.LatticeTree.card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow) and in the comparison of twisted orbital integrals with their shadows that enters the construction of matching Hecke correspondences at inert primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_LatticeTreeBaseChange
import Mathlib.Algebra.Group.Pointwise.Set.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem
LT.LatticeTree.card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (σ : LT.LatticeTree.IntegralAut R K)
    (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (hσϖ : σ.toBase ϖ = ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (b : ℤ) (n : ℕ) (hn : 1 ≤ n) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) =
      algebraMap R K u *
        algebraMap R K ϖ ^ (2 * b + (n : ℤ)))
    (dl : Matrix.GeneralLinearGroup (Fin 2) K)
    (hdl : (dl : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal
        ![algebraMap R K ϖ ^ (b + (n : ℤ)),
          algebraMap R K ϖ ^ b])
    (Tc : Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hTc : ∀ t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ Tc ↔ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ ∧
        ∃ w : Rˣ, Matrix.det (t : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w)
    (St : Matrix.GeneralLinearGroup (Fin 2) K → Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSt : ∀ s t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ St s ↔ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ ∧
        s⁻¹ * t * s ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)))
    (S : Finset (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSsupp : ∀ s ∈ S,
      s⁻¹ * δ * σ.mapGL s ∈
        AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) *
            ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) *
          AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)))
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ,
          ∀ u ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)), s' = t * s * u → s' = s)
    (hcov :
      ∀ x : Matrix.GeneralLinearGroup (Fin 2) K,
        x⁻¹ * δ * σ.mapGL x ∈
          AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) *
              ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) *
            AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) →
        ∃ s ∈ S,
          ∃ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ,
            ∃ u ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)), x = t * s * u) :
    Nat.card
        ↥(LT.LatticeTree.twistedOrbitalBall
            (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) n δ σ \
          LT.LatticeTree.twistedOrbitalBall
            (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n - 1) δ σ) =
      (Tc ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).relIndex
          (AutomorphicForm.sigmaCentralizer σ.mapGL δ) *
        ∑ s ∈ S, (St s).relIndex Tc := by sorry
