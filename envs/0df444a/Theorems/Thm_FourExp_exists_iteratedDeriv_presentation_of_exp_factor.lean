-- Prove2me | Theorems.Thm_FourExp_exists_iteratedDeriv_presentation_of_exp_factor
-- name    : FourExp.exists_iteratedDeriv_presentation_of_exp_factor
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:40:47.88945+00:00
-- url     : https://prove2.me/theorems/75faa454-0195-48c9-8276-574ade5ce1b0
-- title:
--   Derivatives of an exponential polynomial at a grid point, presented from a presentation of the exponential factor
-- statement:
--   Let $x_1, x_2, y_1, y_2, \omega, \omega_1 \in \mathbb{C}$, let $\varphi$ be evaluation at $(\omega, \omega_1)$ on $\mathbb{Z}[X][Y]$, and let $D, E_i, G_j \in \mathbb{Z}[X][Y]$ satisfy $x_i\varphi(D) = \varphi(E_i)$ and $y_j\varphi(D) = \varphi(G_j)$. The length of a polynomial in $\mathbb{Z}[X][Y]$ is the sum of the absolute values of all its integer coefficients. There is $c$ with the following property. Let $S, T, a, b, m, L, d \in \mathbb{N}$ and $\Lambda_1 \in \mathbb{C}$, and let $U_{jk} \in \mathbb{Z}[X][Y]$ ($j, k < T$), of length at most $L$ and of $X$- and $Y$-degree at most $d$, satisfy
--
--   $$\varphi(U_{jk}) = \Lambda_1\, e^{(jx_1 + kx_2)(ay_1 + by_2)}.$$
--
--   Then there are $P_{ijk} \in \mathbb{Z}[X][Y]$ ($i < S$), of length at most $c^{\,c(1+m+S)}(1+m+S+T+a+b)^{\,c(1+m+S)}L$ and of $X$- and $Y$-degree at most $c(1+m+S) + d$, such that for all complex $f_{ijk}$, with $F(z) = \sum_{i,j,k} f_{ijk}\, z^{i} e^{(jx_1 + kx_2)z}$,
--
--   $$\varphi(D)^{m+S}\,\Lambda_1\, F^{(m)}(ay_1 + by_2) = \sum_{i,j,k} f_{ijk}\,\varphi(P_{ijk}).$$
--
--   The derivatives are expanded by Leibniz's rule, and $\varphi(D)^{m+S}$ clears the denominators of $jx_1 + kx_2$ and of the powers of $ay_1 + by_2$; $c$ depends only on $D$, $E_i$ and $G_j$. Only the exponential factor depends on what is known about the exponentials: `FourExp.exists_iteratedDeriv_presentation` presents it through four algebraic exponentials, `FourExp.exists_iteratedDeriv_presentation_column` through two algebraic exponentials and two values of integer polynomials, and this node is the part the two share.
-- source:
--   No single source. It is the presentation step of the proofs of Lemmes 4 and 7 in M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, in the part shared by the four exponentials case and the case of one algebraic column; the derivatives are expanded as in formula (7) there (p. 197). Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- The derivatives of the auxiliary exponential polynomial, presented from a presented
exponential factor.

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, `δ = φ(D)`, `β = j x₁ + k x₂` and `ζ = a y₁ + b y₂`, and
suppose that `δ xᵢ = φ(Eᵢ)` and `δ yⱼ = φ(Gⱼ)`. Let `Λ₁ ∈ ℂ` and integer polynomials `U_{jk}`
(`j, k < T`) present the exponential factor, `φ(U_{jk}) = Λ₁ e^(βζ)`, with lengths (sums of the
absolute values of all integer coefficients) at most `L` and degrees in `X` and in `Y` at most `d`.
Then for `F(z) = ∑_{i<S, j<T, k<T} f_{ijk} z^i e^(β z)` with arbitrary complex coefficients,
`δ^(m+S) Λ₁ F⁽ᵐ⁾(ζ) = ∑ f_{ijk} φ(P_{ijk})`, where the `P_{ijk}` do not depend on `f`, have length
at most `c^(c (1+m+S)) (1+m+S+T+a+b)^(c (1+m+S)) L` and degrees at most `c (1+m+S) + d`.

By Leibniz's rule, `(z^i e^(βz))⁽ᵐ⁾(ζ) = ∑_{l ≤ m} C(m,l) i(i-1)⋯(i-l+1) ζ^(i-l) β^(m-l) e^(βζ)`, and
`δ^(m+S) ζ^(i-l) β^(m-l) Λ₁ e^(βζ)` is `φ` of `D^l (j E₀ + k E₁)^(m-l) (a G₀ + b G₁)^(i-l)
D^(S-i+l) U_{jk}`. The constant `c` depends only on `D`, `E`, `G`. This is the part of
`FourExp.exists_iteratedDeriv_presentation` that does not depend on how the exponential factor is
presented; it serves both the four-exponentials case and the column case. -/
theorem exists_iteratedDeriv_presentation_of_exp_factor
    (x₁ x₂ y₁ y₂ : ℂ) (ω ω₁ : ℂ) (D : Polynomial (Polynomial ℤ))
    (E G : Fin 2 → Polynomial (Polynomial ℤ))
    (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j)) :
    ∃ c : ℕ, ∀ (S T a b m : ℕ) (Λ₁ : ℂ) (L d : ℕ)
      (U : Fin T → Fin T → Polynomial (Polynomial ℤ)),
      (∀ j k, ∑ r ∈ (U j k).support, ∑ h ∈ ((U j k).coeff r).support,
          (((U j k).coeff r).coeff h).natAbs ≤ L) →
      (∀ j k r, ((U j k).coeff r).natDegree ≤ d) →
      (∀ j k, (U j k).natDegree ≤ d) →
      (∀ j k : Fin T, Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (U j k) =
        Λ₁ * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) *
          ((a : ℂ) * y₁ + (b : ℂ) * y₂))) →
      ∃ P : Fin S → Fin T → Fin T → Polynomial (Polynomial ℤ),
        (∀ i j k, ∑ r ∈ (P i j k).support, ∑ h ∈ ((P i j k).coeff r).support,
            (((P i j k).coeff r).coeff h).natAbs ≤
          c ^ (c * (1 + m + S)) * (1 + m + S + T + a + b) ^ (c * (1 + m + S)) * L) ∧
        (∀ i j k r, ((P i j k).coeff r).natDegree ≤ c * (1 + m + S) + d) ∧
        (∀ i j k, (P i j k).natDegree ≤ c * (1 + m + S) + d) ∧
        ∀ f : Fin S → Fin T → Fin T → ℂ,
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ^ (m + S) * Λ₁ *
              iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
                f i j k * z ^ (i : ℕ) *
                  Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
              ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
            ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              f i j k *
                Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (P i j k) := by
  sorry

end FourExp
