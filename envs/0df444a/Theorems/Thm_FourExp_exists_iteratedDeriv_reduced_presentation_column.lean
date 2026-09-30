-- Prove2me | Theorems.Thm_FourExp_exists_iteratedDeriv_reduced_presentation_column
-- name    : FourExp.exists_iteratedDeriv_reduced_presentation_column
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:40:42.329208+00:00
-- url     : https://prove2.me/theorems/57c79d91-3641-4ba6-9b89-96a35793766f
-- title:
--   The auxiliary function's derivatives as values of reduced integer polynomials in the unknowns, when only e^{x₁y₂} and e^{x₂y₂} are algebraic
-- statement:
--   In the setting of `FourExp.exists_iteratedDeriv_presentation_column`, let moreover $Q \in \mathbb{Z}[X][Y]$ be monic in $Y$ with $\varphi(Q) = 0$. There is $c$ such that for all $S, T, M, a, b, m$ there are $\Lambda \neq 0$ with $|\Lambda| \le c^{\,c(1+m+S+T(a+b))}$ and, for each index $(i, j, k, \mu, \nu)$ with $\mu < M$ and $\nu < \deg_Y Q$, a polynomial $R_{ijk\mu\nu} \in \mathbb{Z}[X][Y]$ of $Y$-degree below $\deg_Y Q$, length at most $c^{\,c(1+m+S+T(a+b))}(1+m+S+T+a+b)^{\,c(1+m+S)}$ and $X$-degree at most $M + c(1+m+S+Ta)$, such that for every integer array $q$,
--
--   $$\Lambda\, F_q^{(m)}(ay_1 + by_2) = \varphi\Big(\sum q_{ijk\mu\nu}\, R_{ijk\mu\nu}\Big), \qquad F_q(z) = \sum_{i,j,k}\Big(\sum_{\mu,\nu} q_{ijk\mu\nu}\,\omega^{\mu}\omega_1^{\nu}\Big) z^{i} e^{(jx_1 + kx_2)z}.$$
--
--   This is `FourExp.exists_iteratedDeriv_reduced_presentation` with only $e^{x_1y_2}$ and $e^{x_2y_2}$ assumed algebraic: the $X$-degree bound $M + c(1+m+S)$ becomes $M + c(1+m+S+Ta)$, and the other bounds are unchanged. The coefficients of $\sum qR$ are the equations of the linear system of Lemme 4 of Waldschmidt (1973), and $\sum qR$ is the polynomial whose norm is taken in Lemme 7. This conclusion is the hypothesis of `FourExp.aux_linear_system_column`, `FourExp.auxiliary_function_alg_column` and `FourExp.norm_to_polynomial_alg_column`.
-- source:
--   A step in the proofs of Lemmes 4 and 7 of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202 (pp. 197 and 200). Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- The derivatives of the auxiliary function with integer unknowns, as values of integer
polynomials reduced modulo `Q`, in the column case.

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, and let `Q ∈ ℤ[X][Y]` be monic in `Y` with
`φ(Q) = 0`. The unknowns are integers `q_{ijkμν}` with `i < S`, `j, k < T`, `μ < M`,
`ν < deg Q`, and the auxiliary function is
`F_q(z) = ∑ (∑_{μ,ν} q_{ijkμν} ω^μ ω₁^ν) z^i e^((j x₁ + k x₂) z)`.
Suppose that `δ = φ(D) ≠ 0`, that `δ xᵢ`, `δ yⱼ` and `δ e^(xᵢ yⱼ)` are values of integer
polynomials under `φ`, and that only the column `e^(x₁ y₂)`, `e^(x₂ y₂)` is algebraic.
Then the unknown `(i, j, k, μ, ν)` gets an integer polynomial `R_{ijkμν}` of `Y`-degree below
`deg Q`, and `Λ F_q⁽ᵐ⁾(a y₁ + b y₂) = φ(∑ q_{ijkμν} R_{ijkμν})` for every `q`, with `Λ ≠ 0`
independent of `q`. The sizes are those of `FourExp.exists_iteratedDeriv_reduced_presentation`,
except that the `X`-degrees are at most `M + c (1 + m + S + T a)`: the powers of `e^(xᵢ y₁)`, read
at the index `a`, are presented through `Hᵢ₀` and cost degree in `ω`. -/
theorem exists_iteratedDeriv_reduced_presentation_column
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp₂ : ∀ i : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * y₂)))
    (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ))
    (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0)
    (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) *
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) :
    ∃ c : ℕ, ∀ S T M a b m : ℕ, ∃ Λ : ℂ, Λ ≠ 0 ∧
      ‖Λ‖ ≤ (c : ℝ) ^ (c * (1 + m + S + T * (a + b))) ∧
      ∃ R : Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → Polynomial (Polynomial ℤ),
        (∀ i j k μ ν, (R i j k μ ν).natDegree < Q.natDegree) ∧
        (∀ i j k μ ν, ∑ r ∈ (R i j k μ ν).support, ∑ h ∈ ((R i j k μ ν).coeff r).support,
            (((R i j k μ ν).coeff r).coeff h).natAbs ≤
          c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S))) ∧
        (∀ i j k μ ν r, ((R i j k μ ν).coeff r).natDegree ≤ M + c * (1 + m + S + T * a)) ∧
        ∀ q : Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → ℤ,
          Λ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              (∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
                ((q i j k μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) * z ^ (i : ℕ) *
                Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁
            (∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T, ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
              Polynomial.C (Polynomial.C (q i j k μ ν)) * R i j k μ ν) := by
  sorry

end FourExp
