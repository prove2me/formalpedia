-- Prove2me | Theorems.Thm_FourExp_exists_iteratedDeriv_presentation_column
-- name    : FourExp.exists_iteratedDeriv_presentation_column
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:40:45.507477+00:00
-- url     : https://prove2.me/theorems/2c076a9f-3bad-4cb7-ad6d-a247fba511b3
-- title:
--   Derivatives of an exponential polynomial at a grid point, presented when only e^{x₁y₂} and e^{x₂y₂} are algebraic
-- statement:
--   Let $x_1, x_2, y_1, y_2 \in \mathbb{C}$ with $e^{x_1y_2}$ and $e^{x_2y_2}$ algebraic. Let $\omega, \omega_1 \in \mathbb{C}$ and $D, E_i, G_j, H_{ij} \in \mathbb{Z}[X][Y]$ with $\varphi(D) \neq 0$ and $x_i\varphi(D) = \varphi(E_i)$, $y_j\varphi(D) = \varphi(G_j)$, $e^{x_iy_j}\varphi(D) = \varphi(H_{ij})$, where $\varphi$ is evaluation at $(\omega, \omega_1)$. Then there is $c$ such that for all $S, T, a, b, m$ there are $\Lambda \neq 0$ with $|\Lambda| \le c^{\,c(1+m+S+T(a+b))}$ and polynomials $P_{ijk} \in \mathbb{Z}[X][Y]$ ($i < S$, $j, k < T$), of length (the sum of the absolute values of all integer coefficients) at most $c^{\,c(1+m+S+T(a+b))}(1+m+S+T+a+b)^{\,c(1+m+S)}$ and of $X$- and $Y$-degree at most $c(1+m+S+Ta)$, such that for all complex $f_{ijk}$, with $F(z) = \sum_{i,j,k} f_{ijk}\, z^{i} e^{(jx_1 + kx_2)z}$,
--
--   $$\Lambda\, F^{(m)}(ay_1 + by_2) = \sum_{i,j,k} f_{ijk}\,\varphi(P_{ijk}).$$
--
--   This is `FourExp.exists_iteratedDeriv_presentation` with only one column of exponentials assumed algebraic, and a step in Lemmes 4 and 7 of Waldschmidt (1973); the degree bound $c(1+m+S)$ becomes $c(1+m+S+Ta)$. At $ay_1 + by_2$ the exponential factor is $(e^{x_1y_1})^{ja}(e^{x_1y_2})^{jb}(e^{x_2y_1})^{ka}(e^{x_2y_2})^{kb}$. The powers of the algebraic column are reduced through integer relations and cost only height, while $\varphi(D)^{Ta}(e^{x_iy_1})^{n} = \varphi(H_{i1}^{n}D^{Ta-n})$ for $n \le Ta$ costs degree in $\omega$. `FourExp.exists_iteratedDeriv_presentation_of_exp_factor` gives the rest.
-- source:
--   A step in the proofs of Lemmes 4 and 7 of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202 (pp. 197 and 200). Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- Denominators and sizes of the derivatives of the auxiliary exponential polynomial at the
points `a y₁ + b y₂`, in the column case.

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]` and `δ = φ(D) ≠ 0`, and suppose that `δ xᵢ`, `δ yⱼ`
and `δ e^(xᵢ yⱼ)` are values of integer polynomials under `φ`, with the column `e^(x₁ y₂)`,
`e^(x₂ y₂)` algebraic. For `F(z) = ∑_{i<S, j<T, k<T} f_{ijk} z^i e^((j x₁ + k x₂) z)` with
arbitrary complex coefficients, `Λ F⁽ᵐ⁾(a y₁ + b y₂) = ∑ f_{ijk} φ(P_{ijk})` with `Λ ≠ 0` and
`P_{ijk} ∈ ℤ[X][Y]` not depending on `f`.

At `ζ = a y₁ + b y₂` the exponential factor is
`e^(x₁y₁)^(ja) e^(x₂y₁)^(ka) e^(x₁y₂)^(jb) e^(x₂y₂)^(kb)`. The column powers are reduced through
integer annihilators, as in `FourExp.exists_iteratedDeriv_presentation`, and cost no degree. The
powers `n ≤ T a` of `e^(xᵢ y₁)` are presented as `δ^(T a) αⁿ = φ(Hᵢ₀ⁿ D^(T a - n))`, which adds
`c T a` to the degrees in `X` and in `Y`. The length and `Λ` bounds keep the shape of the
four-exponentials case. -/
theorem exists_iteratedDeriv_presentation_column
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp₂ : ∀ i : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * y₂)))
    (ω ω₁ : ℂ) (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ))
    (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0)
    (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) *
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) :
    ∃ c : ℕ, ∀ S T a b m : ℕ, ∃ Λ : ℂ, Λ ≠ 0 ∧ ‖Λ‖ ≤ (c : ℝ) ^ (c * (1 + m + S + T * (a + b))) ∧
      ∃ P : Fin S → Fin T → Fin T → Polynomial (Polynomial ℤ),
        (∀ i j k, ∑ r ∈ (P i j k).support, ∑ h ∈ ((P i j k).coeff r).support,
            (((P i j k).coeff r).coeff h).natAbs ≤
          c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S))) ∧
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S + T * a)) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S + T * a)) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          Λ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              f i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
            f i j k * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (P i j k) := by
  sorry

end FourExp
