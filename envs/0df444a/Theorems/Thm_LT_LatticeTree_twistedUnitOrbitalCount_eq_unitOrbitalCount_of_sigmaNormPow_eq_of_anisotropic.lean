-- Prove2me | Theorems.Thm_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_anisotropic
-- name    : LT.LatticeTree.twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_anisotropic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/91e0123a-16d7-5c6a-af6b-22a437c351db
-- title:
--   Twisted fixed vertices count equals fixed vertices, anisotropic unit case
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$, let $\varpi \in R$ be irreducible and assume the residue ring $R/(\varpi)$ is finite; let $RE$ be a discrete valuation domain with fraction field $E$, and let $\iota$ be an [`LT.LatticeTree.IntegralHom`](def/LatticeTreeBaseChange.html#L15) from $(R,K)$ to $(RE,E)$, that is, a ring homomorphism $\iota.\mathrm{toField} : K \to E$ together with a ring homomorphism $\iota.\mathrm{toBase} : R \to RE$ compatible with the two structure maps. Assume $\iota.\mathrm{toBase}\,\varpi$ is irreducible in $RE$ and that for some $n \in \mathbb{N}$ one has $\#(RE/(\iota.\mathrm{toBase}\,\varpi)) = \#(R/(\varpi))^{n}$. Let $\sigma$ be an [`LT.LatticeTree.IntegralAut`](def/LatticeTreeOrbital.html#L1013) of $(RE,E)$, i.e. a pair of ring automorphisms of $E$ and of $RE$ compatible with the structure map, such that $\sigma$ fixes every element of $\iota.\mathrm{toBase}(R)$, the $n$-th iterate of $\sigma$ on $RE$ is the identity, and every element of $RE$ fixed by $\sigma$ lies in the image of $\iota.\mathrm{toBase}$. Let $d \in \mathbb{N}$, let $\gamma \in \mathrm{GL}_2(R)$, let $\mathrm{mu} \in R^{\times}$ and let $Y$ be a $2 \times 2$ matrix over $R$ with $\gamma_{ij} = \mathrm{mu}\cdot \delta_{ij} + \varpi^{d} Y_{ij}$ for all $i,j$, and assume the reduction of $Y$ modulo $\varpi$ is anisotropic in the sense that for all $a \in R/(\varpi)$ and $v \in (R/(\varpi))^{2}$, $\bar{Y} v = a v$ forces $v = 0$. Let $\delta \in \mathrm{GL}_2(E)$ satisfy $\mathrm{sigmaNormPow}$ of $\delta$ for the map induced by $\sigma$ on $\mathrm{GL}_2(E)$ at length $n$, namely $\delta\,\sigma(\delta)\cdots\sigma^{n-1}(\delta)$, equal to the image under $\iota.\mathrm{mapGL}$ of $\gamma$ pushed to $\mathrm{GL}_2(K)$. Then the cardinality of the set of vertices $v$ of the tree of $(RE,E)$ with `IsTwistedFixedVertex δ σ v` equals the cardinality of the set of vertices of the tree of $(R,K)$ satisfying `IsFixedVertex` for the image of $\gamma$ in $\mathrm{GL}_2(K)$.
--
--   This is the unit case of the fundamental lemma for base change of $\mathrm{GL}_2$ along an unramified cyclic extension, in the geometric form of a comparison of twisted and ordinary fixed-point counts on the Bruhat–Tits tree, for a regular elliptic class written as a unit scalar plus $\varpi^{d}$ times an anisotropic matrix. It is used in the comparison of twisted orbital integrals with ordinary ones, via [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime) and [`AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_anisotropic.lean

import Definitions.Def_LatticeTreeBaseChange
import Definitions.Def_TwistedNormClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Matrix

theorem LT.LatticeTree.twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_anisotropic
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : LT.LatticeTree.IntegralHom R K RE E) (hϖE : Irreducible (ι.toBase ϖ))
    (n : ℕ) (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n)
    (σ : LT.LatticeTree.IntegralAut RE E) (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (d : ℕ) (γ : Matrix.GeneralLinearGroup (Fin 2) R) (mu : Rˣ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hY : ∀ i j,
      (γ : Matrix (Fin 2) (Fin 2) R) i j = (mu : R) * (1 : Matrix (Fin 2) (Fin 2) R) i j + ϖ ^ d * Y i j)
    (hanis : ∀ (a : R ⧸ Ideal.span {ϖ}) (v : Fin 2 → R ⧸ Ideal.span {ϖ}),
      (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})) *ᵥ v = a • v → v = 0)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E)
    (hnorm : LT.TwistedNorm.sigmaNormPow σ.mapGL n δ =
      ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ)) :
    LT.LatticeTree.twistedUnitOrbitalCount δ σ =
      LT.LatticeTree.unitOrbitalCount R (Matrix.GeneralLinearGroup.map (algebraMap R K : R →+* K) γ) := by sorry
