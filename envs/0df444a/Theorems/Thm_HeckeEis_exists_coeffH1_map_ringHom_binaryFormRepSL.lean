-- Prove2me | Theorems.Thm_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL
-- name    : HeckeEis.exists_coeffH1_map_ringHom_binaryFormRepSL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/3cf0beb0-8f72-5847-948d-4cd6d91e9394
-- title:
--   Change of coefficients on H¹(Γ₀(N),Symⁿ) along a ring map
-- statement:
--   Let $\varphi\colon R\to R'$ be a homomorphism of commutative rings and let $n,N$ be natural numbers. Write $\rho_R$ for the representation of $\Gamma_0(N)$ obtained by restricting [`HeckeEis.binaryFormRepSL R n`](def/HeckeEis_BinaryFormRep.html#L61) along the inclusion of $\Gamma_0(N)$ into $SL(2,\mathbb Z)$, that is, the action of $\Gamma_0(N)$ on the degree-$n$ homogeneous part of $R[X_0,X_1]$ by the substitution $X_j\mapsto\sum_i g_{ij}X_i$, and $\rho_{R'}$ for its analogue over $R'$; here `coeffH1` of a representation is the quotient of the module of inhomogeneous $1$-cocycles $z(gh)=z(g)+\rho(g)z(h)$ by those that are coboundaries, with `coeffH1Mk` the class map. The assertion is that there exists an additive homomorphism $\Phi\colon\mathrm{coeffH1}(\rho_R)\to\mathrm{coeffH1}(\rho_{R'})$ with five properties. (1) For every $1$-cocycle $z$ over $R$ there is a $1$-cocycle $w$ over $R'$ with $w(g)=\mathrm{MvPolynomial.map}\,\varphi\,(z(g))$ for all $g\in\Gamma_0(N)$ and $\Phi[z]=[w]$. (2) $\Phi(c\cdot x)=\varphi(c)\cdot\Phi(x)$ for $c\in R$. (3) For every nonzero $\ell$, every $R$-linear $T$ on $\mathrm{coeffH1}(\rho_R)$ and $R'$-linear $T'$ on $\mathrm{coeffH1}(\rho_{R'})$: if $T$ and $T'$ both satisfy [`HeckeEis.IsCoeffHeckeOnH1`](def/Gamma0CoeffCohomologyEigen.html#L61) at level $N$ and index $\ell$, i.e. each sends the class of a cocycle $z$ to the class of the cocycle given by the explicit cochain-level sum `coeffHeckeFun N ℓ` over the finite quotient by `heckeUpper N ℓ` with coefficient part `binaryFormAlphaAdj` (substitution by $\mathrm{diag}(\ell,1)$, i.e. $P(X_0,X_1)\mapsto P(\ell X_0,X_1)$) over $R$, respectively $R'$, then $\Phi(Tx)=T'(\Phi x)$ for all $x$. (4) For every $\pi\in R$ such that $\varphi$ is surjective, $\varphi(a)=0$ if and only if $\pi\mid a$, and $\pi$ acts regularly on $R$, one has $\Phi x=0$ if and only if $x=\pi\cdot y$ for some $y$. (5) If some additive map $r\colon R'\to R$ satisfies $r(\varphi a)=a$ for all $a\in R$, then $\Phi$ is injective.
--
--   This is the degree-one change-of-coefficients (universal coefficient) statement for the cohomology of $\Gamma_0(N)$ with binary-form coefficients, packaged with semilinearity, Hecke-equivariance, a Bockstein description of the kernel, and an injectivity criterion for additively split $\varphi$. It is used for base change of these cohomology groups and for transporting Hecke eigensystems between coefficient rings, in particular along reduction maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1_map_ringHom_binaryFormRepSL {R R' : Type*} [CommRing R] [CommRing R']
    (φ : R →+* R') (n N : ℕ) :
    ∃ Φ : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+
        HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      (∀ z : ↥(HeckeEis.coeffCocycles
          ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        ∃ w : ↥(HeckeEis.coeffCocycles
          ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          (∀ g : CongruenceSubgroup.Gamma0 N,
              ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R' n)) g : MvPolynomial (Fin 2) R')
                = MvPolynomial.map φ
                    (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) g :
                      MvPolynomial (Fin 2) R))) ∧
          Φ (HeckeEis.coeffH1Mk _ z) = HeckeEis.coeffH1Mk _ w) ∧
      (∀ (c : R) (x : HeckeEis.coeffH1
          ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        Φ (c • x) = φ c • Φ x) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ]
        (T : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          →ₗ[R] HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype))
        (T' : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          →ₗ[R'] HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        HeckeEis.IsCoeffHeckeOnH1 N ℓ
            ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)
            (HeckeEis.binaryFormAlphaAdj R n ℓ) T →
          HeckeEis.IsCoeffHeckeOnH1 N ℓ
            ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)
            (HeckeEis.binaryFormAlphaAdj R' n ℓ) T' →
          ∀ x, Φ (T x) = T' (Φ x)) ∧
      (∀ π : R, Function.Surjective φ → (∀ a : R, φ a = 0 ↔ π ∣ a) → IsSMulRegular R π →
        ∀ x : HeckeEis.coeffH1
            ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype),
          Φ x = 0 ↔ ∃ y, x = π • y) ∧
      (∀ r : R' →+ R, (∀ a : R, r (φ a) = a) → Function.Injective Φ) := by sorry
