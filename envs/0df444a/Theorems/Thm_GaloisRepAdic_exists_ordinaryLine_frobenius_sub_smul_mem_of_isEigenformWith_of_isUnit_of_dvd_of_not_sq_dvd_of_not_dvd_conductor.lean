-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_ordinaryLine_frobenius_sub_smul_mem_of_isEigenformWith_of_isUnit_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
-- name    : GaloisRepAdic.exists_ordinaryLine_frobenius_sub_smul_mem_of_isEigenformWith_of_isUnit_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/1c324067-23b2-5b2b-ba03-6cae063005c9
-- title:
--   Ordinary line at p with Frobenius acting by aₚ
-- statement:
--   Fix $M\ge 1$, a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb C$, and a weight-two cusp form $h$ for $\Gamma_1(M)$ which is an eigenform with nebentypus $\varepsilon$ in the coefficient sense: writing $a_n(h)$ for the $n$-th coefficient of the $q$-expansion of width $1$, one has $a_1(h)=1$, the relation $a_{\ell n}(h)+\varepsilon(\ell)\,\ell^{\,k-1}\,[\ell\mid n]\,a_{n/\ell}(h)=a_\ell(h)a_n(h)$ for all primes $\ell\nmid M$ and all $n$ (with $k=2$), the relation $a_{\ell n}(h)=a_\ell(h)a_n(h)$ for all primes $\ell\mid M$ and all $n$, and $h(\gamma\tau)=\varepsilon(d)\,(c\tau+d)^2h(\tau)$ for $\gamma=\begin{pmatrix}a&b\\ c&d\end{pmatrix}\in\Gamma_0(M)$. Let $p$ be a prime and $S$ a finite set of naturals. Let $\mathcal O'$ be a complete discrete valuation domain of characteristic zero with finite residue field, complete for its maximal-ideal topology, with $p$ in the maximal ideal. Let $R$ be a commutative ring with an injective ring homomorphism $\mathrm{toC}\colon R\to\mathbb C$, a ring homomorphism $\varphi\colon R\to\mathcal O'$, and elements $b_\ell,e_\ell$ ($\ell\in\mathbb N$) and $a_p$ such that $\mathrm{toC}(b_\ell)=a_\ell(h)$ and $\mathrm{toC}(e_\ell)=\varepsilon(\ell)$ for every prime $\ell$ with $\ell\nmid M$ and $\ell\notin S$, and $\mathrm{toC}(a_p)=a_p(h)$, with $\varphi(a_p)$ a unit of $\mathcal O'$. Let $\rho$ be an adic Galois representation over $\mathcal O'$: a free $\mathcal O'$-module $V$ of rank two, finite over $\mathcal O'$, with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)=(\overline{\mathbb Q}\simeq_{\mathbb Q}\overline{\mathbb Q})$ to $\mathrm{End}_{\mathcal O'}(V)$ such that for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ with $\rho(\sigma)v-v\in\mathfrak m^n\cdot V$ for all $\sigma$ fixing $L$ pointwise and all $v$. Assume: for every prime $\ell\nmid M$ with $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a nonunit of $A$ and every $\sigma$ in the decomposition group of $A$ acting on the residue field of $A$ by $x\mapsto x^{\ell}$, the trace of $\rho(\sigma)$ equals $\varphi(b_\ell)$; the residual representation $\mathrm{ResidueField}(\mathcal O')\otimes_{\mathcal O'}V$ is absolutely irreducible, i.e. irreducible after base change to the algebraic closure of the residue field; $p\mid M$, $p^2\nmid M$ and $p\nmid\operatorname{cond}(\varepsilon)$. Finally let $P$ be a valuation subring of $\overline{\mathbb Q}$ in which $p$ is a nonunit. Then there is an $\mathcal O'$-submodule $L\subseteq V$ such that $L=\mathcal O'\cdot \mathrm{bs}\,0$ for some $\mathcal O'$-basis $\mathrm{bs}$ of $V$ indexed by $\mathrm{Fin}\,2$; $L$ is stable under $\rho(\sigma)$ for every $\sigma$ in the decomposition group of $P$ over $\mathbb Q$; $\rho(\tau)v-v\in L$ for every $\tau$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ and every $v\in V$; and $\rho(\sigma)v-\varphi(a_p)\,v\in L$ for every $v\in V$ and every $\sigma$ in the decomposition group of $P$ acting on the residue field of $P$ by $x\mapsto x^{p}$.
--
--   This is the ordinary filtration at $p$ of Hida, Mazur–Wiles and Wiles, in the case of weight two with $p$ exactly dividing the level and nebentypus unramified at $p$: restricted to a decomposition group at $p$ the representation is upper triangular, inertia acts trivially on the quotient line, and Frobenius acts there by the $U_p$-eigenvalue $a_p$, here transported to an arbitrary lattice whose Frobenius traces away from $M$ and $S$ match the eigenvalues. It is used to establish strict ordinarity at $p$ of the representations attached to primitive forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_ordinaryLine_frobenius_sub_smul_mem_of_isEigenformWith_of_isUnit_of_dvd_of_not_sq_dvd_of_not_dvd_conductor.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial

theorem GaloisRepAdic.exists_ordinaryLine_frobenius_sub_smul_mem_of_isEigenformWith_of_isUnit_of_dvd_of_not_sq_dvd_of_not_dvd_conductor
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (p : ℕ) [Fact p.Prime] (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hpO' : (p : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R) (ap : R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M))
    (hap : toC ap = ModularFormClass.qCoeff h p) (hunit : IsUnit (φ ap))
    (ρ : GaloisRepAdic O')
    (hρ : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          ρ.trace σ = φ (b ℓ))
    (hirr : ρ.residual.IsAbsolutelyIrreducible)
    (hpM : p ∣ M) (hp2 : ¬ p ^ 2 ∣ M) (hpε : ¬ p ∣ ε.conductor)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ L : Submodule O' ρ.V,
      (∃ bs : Module.Basis (Fin 2) O' ρ.V, L = O' ∙ bs 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
        ∀ v : ρ.V, ρ.ρ σ v - φ ap • v ∈ L) := by sorry
