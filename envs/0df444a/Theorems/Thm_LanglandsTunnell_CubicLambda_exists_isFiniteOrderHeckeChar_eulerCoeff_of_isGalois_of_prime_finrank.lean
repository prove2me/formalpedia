-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_of_isGalois_of_prime_finrank
-- name    : LanglandsTunnell.CubicLambda.exists_isFiniteOrderHeckeChar_eulerCoeff_of_isGalois_of_prime_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/b5acfd5d-9ea7-5ab3-816a-9f2301e544b1
-- title:
--   Order-ℓ Hecke character attached to a prime-degree Galois extension
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an $E$-algebra such that $F/E$ is Galois, and assume the degree $\ell = [F:E]$ is prime. Then there is a homomorphism $\psi : (\mathbb{A}_E)^\times \to \mathbb{C}^\times$ on the units of the adele ring of $E$ which satisfies `IsFiniteOrderHeckeChar E ψ`, that is: $\psi$ is trivial on the image of $E^\times$ under the diagonal embedding into the ideles, $\psi$ is continuous, and $\psi$ is of finite order; moreover $\psi^{\ell} = 1$; and for every height-one prime $\mathfrak{q}$ of $\mathcal{O}_E$ and every height-one prime $\mathfrak{Q}$ of $\mathcal{O}_F$ lying over $\mathfrak{q}$ (i.e. with $\mathfrak{Q}$ contracting to $\mathfrak{q}$), the Euler coefficient of $\psi$ at $\mathfrak{q}$ behaves as follows: if the ramification index $e(\mathfrak{Q}/\mathfrak{q})$ equals $1$, it is a primitive root of unity of order the inertia degree $f(\mathfrak{Q}/\mathfrak{q})$, and if $e(\mathfrak{Q}/\mathfrak{q}) \neq 1$ it is $0$. Here the Euler coefficient `eulerCoeff E ψ 𝔮` is, by definition, the value of $\psi$ on the uniformiser idele at $\mathfrak{q}$ when $\psi$ is unramified at $\mathfrak{q}$ (meaning its local component at $\mathfrak{q}$ kills every local unit $t$ with both $t$ and $t^{-1}$ in the local integers), and $0$ otherwise.
--
--   This is the global class-field-theoretic input for a cyclic extension of prime degree: Artin reciprocity provides a finite-order idele class character of $E$ of order dividing $\ell$ cutting out $F$, with its Euler coefficients at unramified primes given by roots of unity of order the residue degree and vanishing at ramified primes. It is used in the cubic-induction step of the Langlands–Tunnell argument, where the character attached to a cubic extension is induced to an automorphic form, and in the construction of admissible twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_of_isGalois_of_prime_finrank.lean

import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField HeckeCharacter

theorem LanglandsTunnell.CubicLambda.exists_isFiniteOrderHeckeChar_eulerCoeff_of_isGalois_of_prime_finrank
    (E : Type) [Field E] [NumberField E] (F : Type) [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (hℓ : (Module.finrank E F).Prime) :
    ∃ ψ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ, IsFiniteOrderHeckeChar E ψ ∧ ψ ^ Module.finrank E F = 1 ∧
      (∀ (𝔮 : HeightOneSpectrum (𝓞 E)) (𝔔 : HeightOneSpectrum (𝓞 F)), 𝔔.under (𝓞 E) = 𝔮 →
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 →
          IsPrimitiveRoot (eulerCoeff E ψ 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal)) ∧
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal ≠ 1 → eulerCoeff E ψ 𝔮 = 0)) := by sorry
