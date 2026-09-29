-- Prove2me | Theorems.Thm_FourExp_aux_linear_system
-- name    : FourExp.aux_linear_system
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-17T10:21:07.149089+00:00
-- url     : https://prove2.me/theorems/278448f6-4953-4e99-acc6-da2040046df5
-- title:
--   A sufficient integer linear system for the auxiliary function (Waldschmidt 1973, Lemma 4)
-- statement:
--   **The vanishing conditions as an integer linear system.** Let $x_1, x_2, y_1, y_2 \in \mathbb{C}$, suppose every $e^{x_iy_j}$ is algebraic, and suppose $\omega$ is transcendental; $\omega_1$ is a root of $Q \in \mathbb{Z}[X][Y]$, monic in $Y$ of degree $d \ge 1$ and minimal (no non-zero $A$ with $\deg_Y A < d$ vanishes at $(\omega,\omega_1)$); and $x_i$, $y_j$, $e^{x_iy_j}$ are quotients by a common $D$ of elements of $\mathbb{Z}[X][Y]$ evaluated at $(\omega,\omega_1)$. Then there is $\kappa_1 > 0$ such that for every large $N$, with
--   $$S = \lfloor N^2/\sqrt{\log N}\rfloor,\quad t_1 = \lfloor N/\sqrt{\log N}\rfloor,\quad t_2 = \lfloor N\sqrt{\log N}\rfloor,$$
--   there are an integer $M$ with $0 < M \le \kappa_1 S$ and an $R \times U$ integer matrix $B$, where $U = S\,(2N)^2\,M\,d$ and $2R \le U$, with entries at most $e^{\kappa_1 N^2\sqrt{\log N}}$ in absolute value, such that: for every integer vector $q = (q(i,j,k',\mu,\nu))$ with $Bq = 0$, the function
--   $$F(z) = \sum_{i<S}\sum_{j,k'<2N} c(i,j,k')\,z^i e^{(jx_1+k'x_2)z},\qquad c(i,j,k') = \sum_{\mu<M,\,\nu<d} q(i,j,k',\mu,\nu)\,\omega^\mu\omega_1^\nu,$$
--   satisfies $F^{(m)}(ay_1+by_2) = 0$ for all $a < t_1$, $b < t_2$, $m < S$.
--
--   **Proof plan.** Multiply each value $F^{(m)}(ay_1+by_2)$ by a common non-zero denominator and expand it as an integer combination of $\omega^h\omega_1^k$ ($k < d$), reducing powers of $\omega_1$ modulo $Q$. The powers of the algebraic numbers $e^{x_iy_j}$ reduce through their own minimal polynomials, so they add height but not degree in $\omega$. Each condition then contributes about $(M + cS)\,d$ integer linear forms in $q$, with $t_1t_2 \le N^2$ conditions, so $M \ge (c+1)S$ gives $2R \le U$. Coefficient sizes come from $S\log S \approx 2N^2\sqrt{\log N}$ and exponents up to $2N^2\sqrt{\log N}$.
--
--   **Role.** The arithmetic half of `FourExp.auxiliary_function_alg`. Only sufficiency is claimed: the forms need not be independent. The hypotheses are satisfiable.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemma 4 (the equation count).

import Mathlib

namespace FourExp

theorem aux_linear_system
        (x₁ x₂ y₁ y₂ : ℂ)
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j))) (ω ω₁ : ℂ) (hω : Transcendental ℚ ω) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic) (hQd : 0 < Q.natDegree)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0) (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) :
    ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ κ₁ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ ∧ ∃ R : ℕ, 2 * R ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N) * M * Q.natDegree ∧
      ∃ B : Fin R → Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
        (∀ e i j k' μ ν, |((B e i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ₁ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
        ∀ q : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
          (∀ e, ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N), ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, B e i j k' μ ν * q i j k' μ ν = 0) →
          ∀ a b m : ℕ, a < ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ → m < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
            iteratedDeriv m (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0 := by
  sorry

end FourExp
