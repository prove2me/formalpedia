-- Prove2me | Theorems.Thm_ModularCurve_mazurRealizationFamily_of_modRepIsIrreducible_of_isUnramifiedAt
-- name    : ModularCurve.mazurRealizationFamily_of_modRepIsIrreducible_of_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/5a8c8f92-4dc0-5143-aa50-435bb4147def
-- title:
--   Realising the irreducible mod p representation inside J₀(Nq)[𝔪]
-- statement:
--   Let $p$ be a prime with $p\neq 2$ and let $W$ be a Weierstrass model over $\mathbb Z$ with $\Delta_W\neq 0$. Assume: the group of $p$-torsion points of $W_{\mathbb Q}$ over $\overline{\mathbb Q}$ (realised as `AlgebraicClosure ℚ`) has exactly $p^{2}$ elements; the representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on this $\mathbb Z/p$-module satisfies the project's predicate [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17), i.e. there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every automorphism fixing $L$ pointwise acts as the identity; and `W.ModRepIsIrreducible p` holds, i.e. the $p$-torsion module is nontrivial and its only Galois-stable $\mathbb Z/p$-submodules are $\bot$ and $\top$. Let $q$ be a prime, $q\neq p$, and assume that the residual representation `residualGaloisRepOf` attached to these data is unramified at $q$: for every valuation subring $A\subseteq\overline{\mathbb Q}$ with $q$ a nonunit of $A$ and every $\sigma$ in the inertia subgroup of $A$ over $\mathbb Q$, $\sigma$ acts trivially on the $p$-torsion. The conclusion is: for every $N\geq 1$ with $q\nmid N$ such that $W$ is residually modular of level $Nq$ — that is, there are a normalised weight-$2$ eigenform on $\Gamma_0(Nq)$ and a maximal ideal of the integral closure of $\mathbb Z$ in $\mathbb C$ containing $p$ modulo which the coefficients $a_\ell$ agree with $a_\ell(W)$ for all primes $\ell\nmid Nq$, $\ell\neq p$, of good reduction for $W$ — there exists a maximal ideal $\mathfrak m$ of the abstract Hecke algebra `HeckeAlg`$=\mathbb Z[X_\ell:\ell\text{ prime}]$ with: $p\in\mathfrak m$; $\mathfrak m$ not eventually Eisenstein (there is no finite set $S$ of primes with $X_\ell-(\ell+1)\in\mathfrak m$ for all $\ell\notin S$); and $X_\ell-a_\ell(W)\in\mathfrak m$ for every prime $\ell\nmid Nq$, $\ell\neq p$, of good reduction; and moreover there exist a type $V$ carrying an abelian group structure, a module structure over `HeckeAlg ⧸ 𝔪`, an action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ commuting with the scalars, and an additive map $\iota:V\to J_0(Nq)$ (the degree-zero divisor class group `JZero (N*q)` of the level-$Nq$ modular function field over $\overline{\mathbb Q}$), such that $\dim_{\mathrm{HeckeAlg}/\mathfrak m}V=2$, $\iota$ is injective, Galois-equivariant, lands in the $\mathfrak m$-torsion of $J_0(Nq)$ for the Hecke module structure `heckeModuleBar (N*q)`, and intertwines the Hecke action through the quotient map; and finally, for every valuation subring $A\subseteq\overline{\mathbb Q}$ lying over $q$, the inertia subgroup of $A$ over $\mathbb Q$ acts trivially on $V$, and every Frobenius element at $A$ for $q$ acts on $V$ with determinant equal to the image of $q$ in `HeckeAlg ⧸ 𝔪`.
--
--   This is the realisation step underlying Mazur's principle in Ribet's level-lowering argument: the irreducible mod $p$ representation attached to $W$, with scalars extended to a residue field $\mathbb T/\mathfrak m$ of the abstract Hecke algebra, occurs inside the $\mathfrak m$-torsion of the Jacobian of level $Nq$, and at $q$ it is unramified with Frobenius determinant $q$. Compared with the textbook formulation, the Hecke algebra here is the free polynomial ring on the primes rather than a ring of endomorphisms, the Jacobian is the degree-zero divisor class group of the modular function field, and the output is packaged as an explicit two-dimensional $\mathbb T/\mathfrak m$-module together with an injective Galois- and Hecke-equivariant map into $J_0(Nq)$, rather than as an abstract isomorphism of representations. It supplies exactly the data consumed by the level-lowering step [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf), which removes the prime $q$ from a squarefree residual level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mazurRealizationFamily_of_modRepIsIrreducible_of_isUnramifiedAt.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_MazurPrincipleCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem ModularCurve.mazurRealizationFamily_of_modRepIsIrreducible_of_isUnramifiedAt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (hirr : W.ModRepIsIrreducible p) (q : ℕ) [NeZero q] (hq : q.Prime) (hqp : q ≠ p)
    (hunr : ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q) :
    ∀ (N : ℕ) [NeZero N], ¬ q ∣ N → W.IsResiduallyModularOfLevel p (N * q) →
      ∃ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal ∧ ((p : ℕ) : HeckeAlg) ∈ 𝔪 ∧ ¬ IsEventuallyEisenstein 𝔪 ∧
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N * q → ℓ ≠ p →
          heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ) ∈ 𝔪) ∧
        ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (HeckeAlg ⧸ 𝔪) V)
          (_ : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
          (_ : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (HeckeAlg ⧸ 𝔪) V)
          (ι : V →+ JZero (N * q)),
          Module.finrank (HeckeAlg ⧸ 𝔪) V = 2 ∧ Function.Injective ι ∧
          (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : V), ι (g • v) = g • ι v) ∧
          (letI := heckeModuleBar (N * q); ∀ v : V, ι v ∈ heckeTorsion (JZero (N * q)) 𝔪) ∧
          (letI := heckeModuleBar (N * q);
            ∀ (t : HeckeAlg) (v : V), ι (Ideal.Quotient.mk 𝔪 t • v) = t • ι v) ∧
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ v : V, σ • v = v) ∧
            ∀ frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt frob q →
              LinearMap.det (DistribSMul.toLinearMap (HeckeAlg ⧸ 𝔪) V frob) = ((q : ℕ) : HeckeAlg ⧸ 𝔪) := by sorry
