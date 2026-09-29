-- Prove2me | Theorems.Thm_LT_LatticeTree_twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
-- name    : LT.LatticeTree.twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/8d99cecd-932f-50c7-b1d8-f3d31b359196
-- title:
--   Twisted fixed-vertex count as an index-weighted double-coset sum
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$ (via a fixed $R$-algebra structure), and let $\sigma$ be an [`LT.LatticeTree.IntegralAut R K`](def/LatticeTreeOrbital.html#L1013), that is, a ring automorphism of $K$ together with a ring automorphism of $R$ compatible with $R \to K$. Assume $\varpi \in R$ is irreducible with finite residue ring $R/(\varpi)$ and is fixed by the automorphism of $R$ attached to $\sigma$. Let $\delta \in \mathrm{GL}_2(K)$ and $u \in R^\times$ with $\det \delta =$ the image of $u$ in $K$. Write $T =$ [`AutomorphicForm.sigmaCentralizer σ.mapGL δ`](def/AutomorphicForm_SigmaCentralizer.html#L10) for the $\sigma$-twisted centraliser $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$, where $\sigma$ acts on $\mathrm{GL}_2(K)$ entrywise, and $U$ for [`AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K))`](def/AutomorphicForm_LocalOrbitalBase.html#L33), the set of $g \in \mathrm{GL}_2(K)$ all of whose entries, and all of whose entries of $g^{-1}$, lie in the image of $R$. Let $T_c$ be a subgroup of $\mathrm{GL}_2(K)$ whose members are exactly the $t \in T$ with $\det t$ the image of some unit of $R$, and for each $s$ let $\mathrm{St}(s)$ be a subgroup whose members are exactly the $t \in T$ with $s^{-1} t s \in U$. Let $S$ be a finite subset of $\mathrm{GL}_2(K)$ such that: $s^{-1}\delta\,\sigma(s) \in U$ for every $s \in S$; distinct elements of $S$ lie in distinct double cosets, in the sense that $s' = t s u$ with $s, s' \in S$, $t \in T$, $u \in U$ forces $s' = s$; and every $x \in \mathrm{GL}_2(K)$ with $x^{-1}\delta\,\sigma(x) \in U$ is of the form $t s u$ with $s \in S$, $t \in T$, $u \in U$. Then [`LT.LatticeTree.twistedUnitOrbitalCount δ σ`](def/LatticeTreeOrbital.html#L2076), the cardinality of the set of vertices $v$ of the lattice tree of $(R,K)$ satisfying the predicate `IsTwistedFixedVertex δ σ`, equals the relative index of $T_c \sqcup Z$ in $T$, where $Z$ is the centre of $\mathrm{GL}_2(K)$ (that is, the index of $T \cap (T_c \sqcup Z)$ in $T$), multiplied by $\sum_{s \in S} [\,T_c : T_c \cap \mathrm{St}(s)\,]$.
--
--   This is the local geometric count underlying twisted orbital integrals at a place where the relevant automorphism fixes a uniformiser: the set of $\delta$-twisted fixed points on the tree of $\mathrm{GL}_2(K)$ is counted by the twisted double cosets $T s U$ meeting the integral unit set, each weighted by an index of stabilisers. It is used for the untwisted analogue [`LT.LatticeTree.unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap`](thm.html#LT.LatticeTree.unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap), for the identification of a twisted orbital integral with its shadow in [`AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly), and for the construction of matching local Hecke operators at an inert prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_LatticeTreeOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
LT.LatticeTree.twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (σ : LT.LatticeTree.IntegralAut R K)
    (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (hσϖ : σ.toBase ϖ = ϖ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u)
    (Tc : Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hTc : ∀ t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ Tc ↔ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ ∧
        ∃ w : Rˣ, Matrix.det (t : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w)
    (St : Matrix.GeneralLinearGroup (Fin 2) K → Subgroup (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSt : ∀ s t : Matrix.GeneralLinearGroup (Fin 2) K,
      t ∈ St s ↔ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ ∧
        s⁻¹ * t * s ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)))
    (S : Finset (Matrix.GeneralLinearGroup (Fin 2) K))
    (hSsupp : ∀ s ∈ S, s⁻¹ * δ * σ.mapGL s ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)))
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ,
          ∀ u ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)), s' = t * s * u → s' = s)
    (hcov :
      ∀ x : Matrix.GeneralLinearGroup (Fin 2) K,
        x⁻¹ * δ * σ.mapGL x ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) →
        ∃ s ∈ S,
          ∃ t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ,
            ∃ u ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)), x = t * s * u) :
    LT.LatticeTree.twistedUnitOrbitalCount δ σ =
      (Tc ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).relIndex
          (AutomorphicForm.sigmaCentralizer σ.mapGL δ) *
        ∑ s ∈ S, (St s).relIndex Tc := by sorry
