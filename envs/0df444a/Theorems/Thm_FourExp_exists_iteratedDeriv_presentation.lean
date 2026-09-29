-- Prove2me | Theorems.Thm_FourExp_exists_iteratedDeriv_presentation
-- name    : FourExp.exists_iteratedDeriv_presentation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T16:44:03.152988+00:00
-- url     : https://prove2.me/theorems/014c4a25-8d7b-43c6-b2ea-cdf3dab3ca82
-- title:
--   Derivatives of an exponential polynomial at a grid point, presented through the four exponentials
-- statement:
--   Let $x_1, x_2, y_1, y_2 \in \mathbb{C}$ with every $e^{x_i y_j}$ algebraic. Let $\omega, \omega_1 \in \mathbb{C}$ and $D, E_i, G_j, H_{ij} \in \mathbb{Z}[X][Y]$ with $\varphi(D) \neq 0$ and $x_i\varphi(D) = \varphi(E_i)$, $y_j\varphi(D) = \varphi(G_j)$, $e^{x_iy_j}\varphi(D) = \varphi(H_{ij})$, where $\varphi$ is evaluation at $(\omega, \omega_1)$. Then there is $c$ such that for all $S, T, a, b, m$ there are $\Lambda \neq 0$ with $|\Lambda| \le c^{\,c(1+m+S+T(a+b))}$ and polynomials $P_{ijk} \in \mathbb{Z}[X][Y]$ ($i < S$, $j, k < T$), of length at most $c^{\,c(1+m+S+T(a+b))}(1+m+S+T+a+b)^{\,c(1+m+S)}$ and of $X$- and $Y$-degree at most $c(1+m+S)$, such that for every choice of complex coefficients $f_{ijk}$,
--
--   $$\Lambda \cdot \frac{d^{m}}{dz^{m}}\Big(\sum_{i,j,k} f_{ijk}\, z^{i} e^{(jx_1 + kx_2)z}\Big)\Big|_{z = ay_1 + by_2} = \sum_{i,j,k} f_{ijk}\,\varphi(P_{ijk}).$$
--
--   The identity holds for all coefficients at once, so a consumer may choose them afterwards, for example as unknowns of a linear system.
-- source:
--   A step in the proofs of Lemmas 4 and 7 of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- Denominators and sizes of the derivatives of the auxiliary exponential polynomial at the
points `a y₁ + b y₂`.

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]` and `δ = φ(D) ≠ 0`, and suppose that `δ x_i`, `δ y_j`
and `δ e^(x_i y_j)` are values of integer polynomials under `φ`, with every `e^(x_i y_j)`
algebraic. For the exponential polynomial
`F(z) = ∑_{i<S, j<T, k<T} f_{ijk} z^i e^((j x₁ + k x₂) z)` with arbitrary complex coefficients,
the value `F⁽ᵐ⁾(a y₁ + b y₂)` times a nonzero factor `Λ` not depending on `f` is the combination
`∑ f_{ijk} φ(P_{ijk})`, where the `P_{ijk} ∈ ℤ[X][Y]` do not depend on `f` either. `Λ` is
`δ^(m+S)` times the leading coefficients and powers of `δ` that clear the denominators of
`e^((j x₁ + k x₂)(a y₁ + b y₂))` through integer annihilators of the four exponentials. By
Leibniz's rule, `P_{ijk}` is a sum over `l ≤ m` of products of presentations of `δ^l`,
`(δ(j x₁ + k x₂))^(m-l)`, `δ^S (a y₁ + b y₂)^(i-l)` and `Λ e^((j x₁ + k x₂)(a y₁ + b y₂))`,
which bounds its length (sum of the absolute values of all its integer coefficients) and its
degrees in `X` and in `Y`. The constant `c` depends only on the data, not on
`S, T, a, b, m`. -/
theorem exists_iteratedDeriv_presentation
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)))
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
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S)) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S)) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          Λ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              f i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
            f i j k * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (P i j k) := by
  sorry

end FourExp
