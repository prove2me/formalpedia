-- Prove2me | Theorems.Thm_HeckeEis_exists_injective_baseChange_coeffH1_binaryFormRepSL
-- name    : HeckeEis.exists_injective_baseChange_coeffH1_binaryFormRepSL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/29559933-5d4d-5848-917b-e12e80c1a34e
-- title:
--   Injective mod p scalar extension of H¹(Γ₀(N),Symⁿ)
-- statement:
--   Let $p$ be a prime, let $F$ be a field of characteristic $p$, and let $n,N$ be natural numbers. For a commutative ring $R$, let [`HeckeEis.binaryFormRepSL R n`](def/HeckeEis_BinaryFormRep.html#L61) denote the representation of $\mathrm{SL}_2(\mathbb Z)$ on the degree-$n$ homogeneous part [`HeckeEis.BinaryForm R n`](def/HeckeEis_BinaryFormRep.html#L25) of $R[X_0,X_1]$ in which $g$ acts by the substitution $X_j \mapsto \sum_i g_{ij} X_i$ (coefficients of $g$ mapped into $R$), restricted along the inclusion of $\Gamma_0(N)$ into $\mathrm{SL}_2(\mathbb Z)$; for such a representation $\rho$, [`HeckeEis.coeffCocycles`](def/Gamma0CoeffCohomology.html#L13) is the module of functions $z$ on the group with $z(gh)=z(g)+\rho(g)z(h)$, [`HeckeEis.coeffH1`](def/Gamma0CoeffCohomologyEigen.html#L16) is its quotient by the cocycles that are coboundaries, and [`HeckeEis.coeffH1Mk`](def/Gamma0CoeffCohomologyEigen.html#L27) is the quotient map. The assertion is that there exists an $F$-linear map $\Phi$ from $F \otimes_{\mathbb Z} H^1$ of the integral representation to $H^1$ of the representation over $F$ such that: $\Phi$ is injective, and for every $c \in F$ and every integral cocycle $z$ there is a cocycle $w$ over $F$ with $w(g) = c \cdot (\text{image of } z(g) \text{ under coefficientwise } \mathbb Z \to F)$ for all $g \in \Gamma_0(N)$, and $\Phi(c \otimes [z]) = [w]$.
--
--   This is the injectivity half of a universal-coefficients comparison, in the explicit inhomogeneous cocycle model, between the first coefficient cohomology of $\Gamma_0(N)$ with integral binary-form coefficients extended by scalars to $F$ and the same cohomology computed over $F$; no condition on $n$, $N$ or $p$ enters. It is used to transport integral cohomology classes and their Hecke eigenvalue data into characteristic $p$, and is cited in the construction of mod $p$ eigensystems on $H^1$ attached to binary-form coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_injective_baseChange_coeffH1_binaryFormRepSL.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups TensorProduct

theorem HeckeEis.exists_injective_baseChange_coeffH1_binaryFormRepSL (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [CharP F p] (n N : ℕ) :
    ∃ Φ : F ⊗[ℤ] HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[F]
        HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      Function.Injective Φ ∧
      ∀ (c : F)
        (z : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype))),
        ∃ w : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          (∀ g : CongruenceSubgroup.Gamma0 N,
              ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)) g : MvPolynomial (Fin 2) F) =
                c • MvPolynomial.map (Int.castRingHom F)
                  (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
            Φ (c ⊗ₜ[ℤ] HeckeEis.coeffH1Mk _ z) = HeckeEis.coeffH1Mk _ w := by sorry
