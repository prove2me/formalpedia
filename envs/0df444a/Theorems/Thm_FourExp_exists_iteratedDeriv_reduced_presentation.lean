-- Prove2me | Theorems.Thm_FourExp_exists_iteratedDeriv_reduced_presentation
-- name    : FourExp.exists_iteratedDeriv_reduced_presentation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T16:44:00.654473+00:00
-- url     : https://prove2.me/theorems/e8fbf45e-5c3e-460b-8f33-429a3e02cc84
-- title:
--   The auxiliary function's derivatives as values of reduced integer polynomials in the unknowns
-- statement:
--   In the setting of `FourExp.exists_iteratedDeriv_presentation`, let moreover $Q \in \mathbb{Z}[X][Y]$ be monic in $Y$ with $\varphi(Q) = 0$. There is $c$ such that for all $S, T, M, a, b, m$ there are $\Lambda \neq 0$ with $|\Lambda| \le c^{\,c(1+m+S+T(a+b))}$ and, for each index $(i, j, k, \mu, \nu)$ with $\mu < M$ and $\nu < \deg_Y Q$, a polynomial $R_{ijk\mu\nu} \in \mathbb{Z}[X][Y]$ of $Y$-degree below $\deg_Y Q$, length at most $c^{\,c(1+m+S+T(a+b))}(1+m+S+T+a+b)^{\,c(1+m+S)}$ and $X$-degree at most $M + c(1+m+S)$, such that for every integer array $q$,
--
--   $$\Lambda\, F_q^{(m)}(ay_1 + by_2) = \varphi\Big(\sum q_{ijk\mu\nu}\, R_{ijk\mu\nu}\Big), \qquad F_q(z) = \sum_{i,j,k}\Big(\sum_{\mu,\nu} q_{ijk\mu\nu}\,\omega^{\mu}\omega_1^{\nu}\Big) z^{i} e^{(jx_1 + kx_2)z}.$$
--
--   The coefficients of the reduced polynomial $\sum q R$ are the equations of the auxiliary linear system, and the polynomial itself is the one whose norm is taken afterwards.
-- source:
--   A step in the proofs of Lemmas 4 and 7 of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- The derivatives of the auxiliary function with integer unknowns, as values of integer
polynomials reduced modulo `Q`.

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, and let `Q ∈ ℤ[X][Y]` be monic in `Y` with
`φ(Q) = 0`. The unknowns are integers `q_{ijkμν}` with `i < S`, `j, k < T`, `μ < M`,
`ν < deg Q`, and the auxiliary function is
`F_q(z) = ∑ (∑_{μ,ν} q_{ijkμν} ω^μ ω₁^ν) z^i e^((j x₁ + k x₂) z)`.
Under the hypotheses of the presentation of the derivatives, the unknown `(i, j, k, μ, ν)`
gets the integer polynomial `R_{ijkμν}`, the remainder modulo `Q` of `X^μ Y^ν P_{ijk}`, where
`φ(P_{ijk})` is `Λ` times the `m`-th derivative of `z^i e^((j x₁ + k x₂) z)` at `a y₁ + b y₂`.
It has `Y`-degree below `deg Q`, and `Λ F_q⁽ᵐ⁾(a y₁ + b y₂) = φ(∑ q_{ijkμν} R_{ijkμν})` for every
`q`, with `Λ ≠ 0` independent of `q`. Multiplying by `X^μ Y^ν` does not increase the length (the
sum of the absolute values of all integer coefficients), and the reduction multiplies it by at
most `C` to the power of the `Y`-degree; so the lengths of the `R_{ijkμν}` keep the shape of the
bound on the `P_{ijk}`, and their `X`-degrees are at most `M` plus a multiple of `1 + m + S`. -/
theorem exists_iteratedDeriv_reduced_presentation
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)))
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
        (∀ i j k μ ν r, ((R i j k μ ν).coeff r).natDegree ≤ M + c * (1 + m + S)) ∧
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
