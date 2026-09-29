-- Prove2me | Theorems.Thm_FourExp_norm_to_polynomial
-- name    : FourExp.norm_to_polynomial
-- status  : Open
-- author  : @carlok
-- created : 2026-09-16T12:09:28.527419+00:00
-- url     : https://prove2.me/theorems/320d5b05-3f3c-40b7-be79-53fc549d2d55
-- title:
--   Norms of small values give small integer polynomials (Waldschmidt 1973, Lemma 7)
-- statement:
--   **From a small value to a small polynomial.** Let $x_1, x_2, y_1, y_2 \in \mathbb{C}$ and suppose $\omega$ is transcendental; $\omega_1$ is a root of $Q \in \mathbb{Z}[X][Y]$, monic in $Y$ of degree $d \ge 1$ and minimal, in the sense that no non-zero $A \in \mathbb{Z}[X][Y]$ with $\deg_Y A < d$ vanishes at $(\omega, \omega_1)$; and $D, E_i, G_j, H_{ij} \in \mathbb{Z}[X][Y]$ with $D(\omega,\omega_1) \ne 0$, $x_i D = E_i$, $y_j D = G_j$ and $e^{x_iy_j} D = H_{ij}$ at $(\omega, \omega_1)$. For every $\kappa, \kappa' > 0$ there is $k > 0$ such that for every $C$ there is $N_0$ with the following property, with the parameters below.
--   $$S = \lfloor N^2/\sqrt{\log N}\rfloor,\quad T = 2N,\quad t_1 = \lfloor N/\sqrt{\log N}\rfloor,\quad t_2 = \lfloor N\sqrt{\log N}\rfloor,\quad R_1 = 14t_1,\quad R_2 = 14t_2,\quad S' = \lfloor S/2\rfloor.$$
--   Let $N > N_0$, $M \le \kappa S$ and integers $|q(i,j,k',\mu,\nu)| \le e^{\kappa N^2\sqrt{\log N}}$, and let $c$ and $F$ be as in `FourExp.auxiliary_function`. If $F^{(s)}(ay_1+by_2) \ne 0$ and $|F^{(s)}(ay_1+by_2)| \le \exp(-N^4\sqrt{\log N}/\kappa')$ for some $a<R_1$, $b<R_2$, $s<S'$, then there is a non-zero $P \in \mathbb{Z}[X]$ with coefficients at most $e^{kN^2\sqrt{\log N}}$, $\deg P \le kN^2/\sqrt{\log N}$ and $|P(\omega)| < e^{-C k^2N^4}$. The statement uses the $N \le 3$ branch of the core's $\sigma_1, \sigma_2$, but that branch is irrelevant for large $N$.
--
--   **Proof sketch.** Multiply the value by a power of $D(\omega,\omega_1)$ and reduce modulo $Q$ to get $A(\omega,\omega_1)$ with $A \in \mathbb{Z}[X][Y]$, $\deg_X A = O(S)$ and $\log H(A) = O(N^2\sqrt{\log N})$. Take $P = \operatorname{Res}_Y(Q, A)$, the norm from $\mathbb{Q}(\omega,\omega_1)$ to $\mathbb{Q}(\omega)$ written as a polynomial. It is non-zero because $A(\omega,\omega_1) \ne 0$ and $Q(\omega, Y)$ is irreducible over $\mathbb{Q}(\omega)$. $|P(\omega)|$ is the small factor times $d-1$ conjugate factors, each $e^{O(N^2\sqrt{\log N})}$, and the $\sqrt{\log N}$ gain beats any $C$.
--
--   The paper's field norm $N_{K/\mathbb{Q}(\omega)}$ is replaced by a resultant. The hypotheses are satisfiable.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemma 7. Superseded: the same defect as FourExp.auxiliary_function, namely the missing hypothesis that the four exponentials are algebraic. Replaced by FourExp.norm_to_polynomial_alg, which is Proved.

import Mathlib

namespace FourExp

theorem norm_to_polynomial
    (x₁ x₂ y₁ y₂ : ℂ) (ω ω₁ : ℂ) (hω : Transcendental ℚ ω) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic) (hQd : 0 < Q.natDegree)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0) (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j))
    (κ κ' : ℝ) (hκ : 0 < κ) (hκ' : 0 < κ') :
    ∃ k : ℝ, 0 < k ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ M : ℕ, (M : ℝ) ≤ κ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
      ∀ q : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
      (∀ i j k' μ ν, |((q i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) →
      ∀ a b s : ℕ, a < 14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < 14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ → s < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ / 2 →
      iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 →
      ‖iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂)‖
          ≤ Real.exp (-(((N : ℝ) ^ 4 * Real.sqrt (Real.log (N : ℝ))) / κ')) →
      ∃ P : Polynomial ℤ, P ≠ 0 ∧
        (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
        (P.natDegree : ℝ) ≤ k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))) ∧
        ‖Polynomial.aeval ω P‖ < Real.exp (-(C * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ)))))) := by
  sorry

end FourExp
