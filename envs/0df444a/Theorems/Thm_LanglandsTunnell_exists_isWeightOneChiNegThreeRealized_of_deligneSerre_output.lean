-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isWeightOneChiNegThreeRealized_of_deligneSerre_output
-- name    : LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_of_deligneSerre_output
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/c8bd05eb-8507-543d-800f-32d0e03508a2
-- title:
--   Descent of Deligne–Serre output to a ℤ[√-2]-valued eigensystem
-- statement:
--   Fix a continuous surjective homomorphism $\rho$ from $\Gamma_{\mathbb Q}=\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{GL}_2(\mathbb Z/3)$ whose determinant is the mod-$3$ cyclotomic character `modThreeCyclotomicChar`, and a monoid homomorphism $\Psi:\mathrm{GL}_2(\mathbb Z/3)\to\mathrm{GL}_2(\mathbb Z[\sqrt{-2}])$ splitting entrywise reduction along `red` (the ring map $\mathbb Z[\sqrt{-2}]\to\mathbb Z/3$ with $\sqrt{-2}\mapsto-1$), so $\Psi(g)$ reduces to $g$. Assume tameness: for every prime $q\neq3$ and every valuation subring $A\subset\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the order of the image under $\rho$ of the inertia subgroup of $A$ is coprime to $q$. Let $\iota:\mathbb Z[\sqrt{-2}]\to\mathbb C$ be a ring map, $\rho_{\mathbb C}$ the entrywise image of $\Psi\circ\rho$ under $\iota$, and let $g$ be a weight-one cusp form on $\Gamma_1(N')$, $N'\neq0$, satisfying the Deligne–Serre conclusions for $\rho_{\mathbb C}$, written in terms of the coefficients `qCoeff` of its $q$-expansion: $a_1=1$; for primes $p\nmid N'$, $A$ over $p$ and $\sigma$ acting as the $q$-power map on the residue field of $A$, $a_p=\operatorname{tr}\rho_{\mathbb C}(\sigma)$ together with the recursion $a_{pn}+\det\rho_{\mathbb C}(\sigma)\,[p\mid n]a_{n/p}=a_pa_n$; full multiplicativity $a_{\ell n}=a_\ell a_n$ for primes $\ell\mid N'$; at primes $\ell$ with inertia image of order coprime to $\ell$, the relation $v_\ell(N')+\dim_{\mathbb C}V^{I}=2$ for the inertia invariants $V^I$ of the matrix representation of $\rho_{\mathbb C}$, and $a_\ell=\operatorname{tr}(\rho_{\mathbb C}(\sigma)|_{V^I})$ for Frobenius elements $\sigma$; and the nebentypus identity $g(\gamma\tau)=\det\rho_{\mathbb C}(\sigma)\,(c\tau+d)g(\tau)$ for $\gamma\in\Gamma_0(N')$ with $d\equiv p \pmod{N'}$, $p\nmid N'$ prime and $\sigma$ Frobenius at $p$. Then there exist $N\neq0$ and $b:\mathbb N\to\mathbb Z[\sqrt{-2}]$ with: $3\mid N$; $q^3\nmid N$ for every prime $q\neq3$; $b$ a formal Hecke eigensystem for the weights $\ell\mapsto0$ if $\ell\mid N$ and $\ell\mapsto\chi_{-3}(\ell)$ otherwise, i.e. $b_1=1$ and $b_{\ell n}+e_\ell[\ell\mid n]b_{n/\ell}=b_\ell b_n$ for all primes $\ell$ and all $n$; [`CuspForm.IsWeightOneChiNegThreeRealized N b`](def/LanglandsTunnell_WeightOneRealizationCarriers.html#L15), i.e. some ring map $\mathbb Z[\sqrt{-2}]\to\mathbb C$ and some weight-one cusp form on $\Gamma_1(N)$ have $q$-expansion coefficients the images of the $b_n$; and $b_p=\operatorname{tr}\Psi(\rho(\sigma))$ for every prime $p\nmid3N$, every $A$ over $p$ and every $\sigma$ that is Frobenius at $p$.
--
--   This is the descent step of the Langlands–Tunnell input to modularity: it converts the analytic output of the Deligne–Serre theorem for the complex lift $\iota\circ\Psi\circ\rho$ into an eigensystem with coefficients in $\mathbb Z[\sqrt{-2}]$, of character type $\chi_{-3}$, carried by a weight-one cusp form whose level is divisible by $3$ and cube-free away from $3$, with Frobenius traces given by $\Psi\circ\rho$ away from $3N$. It feeds [`LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_three_dvd_not_cube_dvd_of_coprime`](thm.html#LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_three_dvd_not_cube_dvd_of_coprime), from which the mod-$3$ representation attached to the Frey curve is shown to be modular.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isWeightOneChiNegThreeRealized_of_deligneSerre_output.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_LanglandsTunnell_WeightOneRealizationCarriers
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm WeierstrassCurve FLT.ExplicitLift EisensteinWeightOne
open CongruenceSubgroup
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_of_deligneSerre_output
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3)) (hρ : Continuous ρ) (hsurj : Function.Surjective ρ)
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g)
    (htame : ∀ q : ℕ, q.Prime → q ≠ 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ)).Coprime q)
    (ι : ℤ√(-2) →+* ℂ) (ρℂ : Γℚ →* GL (Fin 2) ℂ)
    (hρℂ : ρℂ = (Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ))
    (N' : ℕ) [NeZero N'] (g : CuspForm (Gamma1 N') 1)
    (hDS : ModularFormClass.qCoeff g 1 = 1 ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N' →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            ModularFormClass.qCoeff g p =
                ((ρℂ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).trace ∧
            ∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
                ((ρℂ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det *
                  (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
              ModularFormClass.qCoeff g p * ModularFormClass.qCoeff g n) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N' → ∀ n : ℕ,
        ModularFormClass.qCoeff g (ℓ * n) =
          ModularFormClass.qCoeff g ℓ * ModularFormClass.qCoeff g n) ∧
      (∀ ℓ : ℕ, ℓ.Prime →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          (Nat.card ((A.inertiaSubgroupIn ℚ).map ρℂ)).Coprime ℓ →
            N'.factorization ℓ +
                Module.finrank ℂ (Representation.invariants
                  ((Deformation.matrixRepresentation ρℂ).comp
                    (A.inertiaSubgroupIn ℚ).subtype)) = 2 ∧
            ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ →
              ∃ hσ : ∀ v ∈ Representation.invariants
                    ((Deformation.matrixRepresentation ρℂ).comp (A.inertiaSubgroupIn ℚ).subtype),
                  Deformation.matrixRepresentation ρℂ σ v ∈ Representation.invariants
                    ((Deformation.matrixRepresentation ρℂ).comp (A.inertiaSubgroupIn ℚ).subtype),
                ModularFormClass.qCoeff g ℓ =
                  LinearMap.trace ℂ _ ((Deformation.matrixRepresentation ρℂ σ).restrict hσ)) ∧
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 N' →
        ∀ p : ℕ, p.Prime → ¬ p ∣ N' → ((γ 1 1 : ℤ) : ZMod N') = (p : ZMod N') →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
              ∀ τ : UpperHalfPlane,
                g (γ • τ) =
                  ((ρℂ σ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det *
                    ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) * g τ))) :
    ∃ (N : ℕ) (_ : NeZero N) (b : ℕ → ℤ√(-2)),
      3 ∣ N ∧
      (∀ q : ℕ, q.Prime → q ≠ 3 → ¬ q ^ 3 ∣ N) ∧
      FormalHecke.IsEigensystem
        (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
      CuspForm.IsWeightOneChiNegThreeRealized N b ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ 3 * N →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
            b p = ((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))).trace := by sorry
