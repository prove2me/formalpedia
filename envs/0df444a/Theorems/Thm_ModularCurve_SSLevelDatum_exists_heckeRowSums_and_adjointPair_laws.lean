-- Prove2me | Theorems.Thm_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws
-- name    : ModularCurve.SSLevelDatum.exists_heckeRowSums_and_adjointPair_laws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/fc8bf3bc-8be5-5066-b006-a3daea30db9a
-- title:
--   Hecke laws for a supersingular two-level degeneracy datum
-- statement:
--   Let $M, s, q'$ be natural numbers with $M, s$ nonzero, $q'$ and $s$ prime, $q' \ge 5$, $s \neq q'$, and neither $q'$ nor $s$ dividing $M$; let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` whose residue field $\kappa$ has characteristic $q'$, and assume the two sets of supersingular places $\Sigma(Ms) =$ `ssPlaces q' (M*s) κ` and $\Sigma(M) =$ `ssPlaces q' M κ` of the modular function fields of levels $Ms$ and $M$ over $\kappa$ are finite (with decidable equality). Let $X$ be an `SSLevelDatum q' κ M s`, so $X$ provides the two degeneracy inclusions of level $M$ into level $Ms$ together with integrality, supersingular-stability, Atkin–Lehner and Kronecker-congruence data; write $a, b : \Sigma(Ms) \to \Sigma(M)$ for the induced maps `X.degeneracyData.a`, `X.degeneracyData.b`, $w(e) =$ `Nat.toPNat' (placeWidth (M*s) e)` for the edge widths, $w_V(v) =$ `Nat.toPNat' (placeWidth M v)` for the vertex widths (the width read as $1$ when it is $0$), and $T_1(\ell) =$ `X.edgeHecke ℓ`, $T_2(\ell) =$ `X.vertexHecke ℓ` for the Hecke matrices on $\Sigma(Ms)$ and $\Sigma(M)$. Then there exist functions $n_1, n_2 :$ `Nat.Primes` $\to \mathbb{Z}$ such that every column of $T_1(\ell)$ sums to $n_1(\ell)$ and every column of $T_2(\ell)$ sums to $n_2(\ell)$, and $\mathbb{Z}$-linear maps $p^{\mathrm{adj}}_i : (\Sigma(M) \to \mathbb{Z}) \to (\Sigma(Ms) \to \mathbb{Z})$, $i \in \{0,1\}$, carrying the degree-zero lattice `characterLattice` of $\Sigma(M)$ into that of $\Sigma(Ms)$, with all of the following: the $T_1(\ell)$ commute pairwise, and so do the $T_2(\ell)$; for each $i$ and each prime $\ell \neq s$ the incidence matrix [`CerednikDrinfeld.degeneracyMatrix`](def/CerednikDrinfeld_Ribbon.html#L21) of $a$ (for $i=0$) resp. $b$ (for $i=1$), whose $(v,e)$ entry is $1$ exactly when the map sends $e$ to $v$, intertwines $T_1(\ell)$ with $T_2(\ell)$; if $x : \Sigma(Ms) \to \mathbb{Z}$ is annihilated by both incidence matrices then so is $T_1(s)x$, where $s$ is regarded as a prime via `hs`; the weighted symmetries $w(i)\,T_1(\ell)_{ij} = w(j)\,T_1(\ell)_{ji}$ for $\ell \nmid Mq's$ and $w_V(i)\,T_2(\ell)_{ij} = w_V(j)\,T_2(\ell)_{ji}$ for $\ell \nmid Mq'$; $n_1(\ell) = \ell+1$ for $\ell \nmid Mq's$ and $n_2(\ell) = \ell+1$ for $\ell \nmid Mq'$; $T_1(q')$ and $T_2(q')$ are permutation matrices, i.e. there are permutations $\sigma$ of $\Sigma(Ms)$ and of $\Sigma(M)$ with entries $\delta_{i,\sigma j}$; and $p^{\mathrm{adj}}_i$ is adjoint to the corresponding pushforward for the width-weighted pairings, $\sum_v w_V(v)\,(a_*y)(v)\,x(v) = \sum_e w(e)\,y(e)\,(p^{\mathrm{adj}}_i x)(e)$ (resp. with $b$).
--
--   This collects, in one existential package, the combinatorial Hecke structure of the Deuring–Eichler supersingular graph of levels $Ms \rightrightarrows M$ in characteristic $q'$: commutation, intertwining by the degeneracy maps, Frobenius at $q'$ acting as a permutation, the width-weighted self-adjointness of the Hecke operators away from $Mq's$, and the adjoints of the two pushforwards. It is the input for the rank comparisons between the Hecke torsion of the Čerednik–Drinfeld ribbon component group and the corresponding quotients of character lattices, and thence for the bound on the toric monodromy part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws.lean

import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ComponentGroupHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SSLevelDatum.exists_heckeRowSums_and_adjointPair_laws
    (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime] (hs : s.Prime)
    (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s) :
    ∃ (n₁ : Nat.Primes → ℤ) (_ : ∀ ℓ : Nat.Primes, HeckeRowSums (X.edgeHecke ℓ).transpose (n₁ ℓ))
      (n₂ : Nat.Primes → ℤ) (_ : ∀ ℓ : Nat.Primes, HeckeRowSums (X.vertexHecke ℓ).transpose (n₂ ℓ))
      (padj : Fin 2 → ((↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) →ₗ[ℤ]
        (↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ)))
      (_ : ∀ (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ),
        x ∈ characterLattice ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) →
        padj i x ∈ characterLattice ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))),
      (∀ ℓ ℓ' : Nat.Primes, Commute (X.edgeHecke ℓ) (X.edgeHecke ℓ')) ∧
      (∀ ℓ ℓ' : Nat.Primes, Commute (X.vertexHecke ℓ) (X.vertexHecke ℓ')) ∧
      (∀ (i : Fin 2) (ℓ : Nat.Primes), (ℓ : ℕ) ≠ s →
          CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i) * X.edgeHecke ℓ =
            X.vertexHecke ℓ * CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)) ∧
      (∀ x : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ,
          (∀ i : Fin 2,
            (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec x = 0) →
          ∀ i : Fin 2, (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec
            ((X.edgeHecke ⟨s, hs⟩).mulVec x) = 0) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ (M * q') * s →
          ∀ i j, (X.degeneracyData.w i : ℤ) * X.edgeHecke ℓ i j = (X.degeneracyData.w j : ℤ) * X.edgeHecke ℓ j i) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M * q' →
          ∀ i j, (Nat.toPNat' (placeWidth M i.1) : ℤ) * X.vertexHecke ℓ i j =
            (Nat.toPNat' (placeWidth M j.1) : ℤ) * X.vertexHecke ℓ j i) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ (M * q') * s → n₁ ℓ = ((ℓ : ℕ) : ℤ) + 1) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M * q' → n₂ ℓ = ((ℓ : ℕ) : ℤ) + 1) ∧
      (∃ σ : Equiv.Perm ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)),
          ∀ i j, X.edgeHecke ⟨q', Fact.out⟩ i j = if i = σ j then 1 else 0) ∧
      (∃ σ : Equiv.Perm ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)),
          ∀ i j, X.vertexHecke ⟨q', Fact.out⟩ i j = if i = σ j then 1 else 0) ∧
      (∀ (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ)
          (y : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ),
          (∑ v, (Nat.toPNat' (placeWidth M v.1) : ℤ) *
              (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec y v * x v) =
            ∑ e, (X.degeneracyData.w e : ℤ) * y e * padj i x e) := by sorry
