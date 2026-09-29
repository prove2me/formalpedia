-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicLambda_exists_int_jacobiSym_eq_of_finrank_eq_two
-- name    : LanglandsTunnell.CubicLambda.exists_int_jacobiSym_eq_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/f889289f-6c79-5d34-b084-5377858b31cc
-- title:
--   Jacobi symbol detects splitting in a quadratic field
-- statement:
--   Let $L$ be a number field, equipped with an $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_L$ that is integral, and suppose $\dim_{\mathbb{Q}} L = 2$. The assertion is that there exists an integer $d$ with the following properties: $d \neq 0$; $d < 0$ holds if and only if the number of complex infinite places of $L$ is non-zero; and for every prime number $\ell$ such that $\ell$ does not divide $2d$ in $\mathbb{Z}$, for every height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ whose ideal contains the image of $\ell$, and for every height-one prime $\mathfrak{q}$ of $\mathcal{O}_L$ lying under $p$ (that is, with `𝔮.under (𝓞 ℚ) = p`), one has: the ramification index of $p$ in $\mathfrak{q}$ equals $1$; if the inertia degree of $p$ in $\mathfrak{q}$ equals $1$ then the Jacobi symbol $\left(\frac{d}{\ell}\right)$ equals $1$; and if that inertia degree equals $2$ then $\left(\frac{d}{\ell}\right)$ equals $-1$. Here the ramification index and inertia degree are the Mathlib variants `Ideal.ramificationIdx'` and `Ideal.inertiaDeg'`.
--
--   This is the classical description of the decomposition of rational primes in a quadratic field by a Legendre–Jacobi symbol: the discriminant-like integer $d$ is a square root generator of $L$, its sign records whether $L$ is imaginary, and away from $2d$ the symbol $\left(\frac{d}{\ell}\right)$ distinguishes split from inert primes. It is used in the cubic-induction step of the Langlands–Tunnell argument, where quadratic subfields of a cubic-related extension must be matched with quadratic characters, in [`LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three`](thm.html#LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three) and its conductor-bounded variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicLambda_exists_int_jacobiSym_eq_of_finrank_eq_two.lean

import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicLambda.exists_int_jacobiSym_eq_of_finrank_eq_two
    (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
    (hL : Module.finrank ℚ L = 2) :
    ∃ d : ℤ, d ≠ 0 ∧ (d < 0 ↔ InfinitePlace.nrComplexPlaces L ≠ 0) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ (ℓ : ℤ) ∣ 2 * d →
        ∀ (p : HeightOneSpectrum (𝓞 ℚ)), (ℓ : 𝓞 ℚ) ∈ p.asIdeal →
          ∀ (𝔮 : HeightOneSpectrum (𝓞 L)), 𝔮.under (𝓞 ℚ) = p →
            p.asIdeal.ramificationIdx' 𝔮.asIdeal = 1 ∧
              (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 → jacobiSym d ℓ = 1) ∧
              (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 2 → jacobiSym d ℓ = -1) := by sorry
