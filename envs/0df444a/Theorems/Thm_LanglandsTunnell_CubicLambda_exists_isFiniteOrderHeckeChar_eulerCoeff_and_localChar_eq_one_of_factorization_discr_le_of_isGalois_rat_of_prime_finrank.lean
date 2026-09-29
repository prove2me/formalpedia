-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_and_localChar_eq_one_of_factorization_discr_le_of_isGalois_rat_of_prime_finrank
-- name    : LanglandsTunnell.CubicLambda.exists_isFiniteOrderHeckeChar_eulerCoeff_and_localChar_eq_one_of_factorization_discr_le_of_isGalois_rat_of_prime_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/20beec7d-2723-54d0-b574-96f96bd5cce0
-- title:
--   Finite-order Hecke character attached to a prime-degree Galois field
-- statement:
--   Let $F$ be a number field that is Galois over $\mathbb{Q}$ and whose degree $\ell = [F:\mathbb{Q}]$ is prime. Then there is a monoid homomorphism $\psi$ from the idele group $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$ with the following four properties. First, $\psi$ is a finite-order Hecke character of $\mathbb{Q}$ in the sense of `IsFiniteOrderHeckeChar`: it is trivial on the principal ideles, i.e. $\psi(\iota(u)) = 1$ for every $u \in \mathbb{Q}^{\times}$ under the diagonal embedding, it is continuous, and it is of finite order. Second, $\psi^{\ell} = 1$. Third, for every height-one prime $\mathfrak{q}$ of $\mathcal{O}_{\mathbb{Q}} = \mathbb{Z}$ and every height-one prime $\mathfrak{Q}$ of $\mathcal{O}_F$ lying under-wise over $\mathfrak{q}$ (that is, $\mathfrak{Q} \cap \mathcal{O}_{\mathbb{Q}} = \mathfrak{q}$): if the ramification index $e(\mathfrak{Q}/\mathfrak{q})$ equals $1$, then the Euler coefficient $\mathrm{eulerCoeff}\,\mathbb{Q}\,\psi\,\mathfrak{q}$ — which is $\psi$ evaluated at the uniformizer idele at $\mathfrak{q}$ when the local component of $\psi$ at $\mathfrak{q}$ is trivial on all local units that are integral together with their inverses, and $0$ otherwise — is a primitive root of unity of order the inertia degree $f(\mathfrak{Q}/\mathfrak{q})$; while if $e(\mathfrak{Q}/\mathfrak{q}) \neq 1$, then this Euler coefficient is $0$. Fourth, for every $\mathfrak{q}$ and every $m \geq 1$ such that the multiplicity of the rational prime $\mathrm{absNorm}\,\mathfrak{q}$ in $|\mathrm{disc}\,F|$ is at most $m$, the local character $\mathrm{localChar}\,\psi\,\mathfrak{q}$ — the restriction of $\psi$ to the units of the completion $\mathbb{Q}_{\mathfrak{q}}$, placed at the place $\mathfrak{q}$ of the finite adeles and extended by $1$ at the infinite places — is trivial on the higher unit group $\mathrm{higherUnitsAt}\,\mathbb{Q}\,\mathfrak{q}\,m$, consisting of those local units $u$ with $|u| = 1$ and $|u - 1| \leq \exp(-m)$.
--
--   This is the existence statement, over the base field $\mathbb{Q}$, of the cyclic-degree-$\ell$ Hecke character whose Euler coefficients record the splitting behaviour of the primes of $F$, together with a conductor bound tied to the discriminant of $F$ via the conductor–discriminant relation. It supplies the character used in the construction of an admissible twist in the Langlands–Tunnell input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_and_localChar_eq_one_of_factorization_discr_le_of_isGalois_rat_of_prime_finrank.lean

import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal HeckeCharacter LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicLambda.exists_isFiniteOrderHeckeChar_eulerCoeff_and_localChar_eq_one_of_factorization_discr_le_of_isGalois_rat_of_prime_finrank
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] (hℓ : (Module.finrank ℚ F).Prime) :
    ∃ ψ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsFiniteOrderHeckeChar ℚ ψ ∧ ψ ^ Module.finrank ℚ F = 1 ∧
      (∀ (𝔮 : HeightOneSpectrum (𝓞 ℚ)) (𝔔 : HeightOneSpectrum (𝓞 F)), 𝔔.under (𝓞 ℚ) = 𝔮 →
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 →
          IsPrimitiveRoot (eulerCoeff ℚ ψ 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal)) ∧
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal ≠ 1 → eulerCoeff ℚ ψ 𝔮 = 0)) ∧
      ∀ (𝔮 : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ), 1 ≤ m →
        (discr F).natAbs.factorization (Ideal.absNorm 𝔮.asIdeal) ≤ m →
          ∀ u ∈ higherUnitsAt ℚ 𝔮 m, localChar ψ 𝔮 u = 1 := by sorry
