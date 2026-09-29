-- Prove2me | Theorems.Thm_FourExp_auxiliary_function
-- name    : FourExp.auxiliary_function
-- status  : Open
-- author  : @carlok
-- created : 2026-09-16T12:09:30.340212+00:00
-- url     : https://prove2.me/theorems/cf30f7a1-b576-4a5d-b179-f5e90c1f29c3
-- title:
--   Siegel's lemma builds the auxiliary function (Waldschmidt 1973, Lemma 4)
-- statement:
--   **The auxiliary function.** Let $x_1, x_2, y_1, y_2 \in \mathbb{C}$ and suppose $\omega$ is transcendental; $\omega_1$ is a root of $Q \in \mathbb{Z}[X][Y]$, monic in $Y$ of degree $d \ge 1$ and minimal, in the sense that no non-zero $A \in \mathbb{Z}[X][Y]$ with $\deg_Y A < d$ vanishes at $(\omega, \omega_1)$; and $D, E_i, G_j, H_{ij} \in \mathbb{Z}[X][Y]$ with $D(\omega,\omega_1) \ne 0$, $x_i D = E_i$, $y_j D = G_j$ and $e^{x_iy_j} D = H_{ij}$ at $(\omega, \omega_1)$. Then there is $\kappa > 0$ such that for every large $N$, with $S, t_1, t_2$ as below, there are $M \le \kappa S$ and integers $q(i,j,k',\mu,\nu)$, for $i<S$, $j,k'<2N$, $\mu<M$, $\nu<d$, with the following properties.
--   $$S = \lfloor N^2/\sqrt{\log N}\rfloor,\quad T = 2N,\quad t_1 = \lfloor N/\sqrt{\log N}\rfloor,\quad t_2 = \lfloor N\sqrt{\log N}\rfloor,\quad R_1 = 14t_1,\quad R_2 = 14t_2,\quad S' = \lfloor S/2\rfloor.$$
--   - Every $|q| \le e^{\kappa N^2\sqrt{\log N}}$.
--   - Put $c(i,j,k') = \sum_{\mu,\nu} q(i,j,k',\mu,\nu)\,\omega^\mu\omega_1^\nu$. Some $c$ is non-zero, and every $|c| \le e^{\kappa N^2\sqrt{\log N}}$.
--   - The function $F$ below satisfies $F^{(m)}(ay_1+by_2) = 0$ for all $a<t_1$, $b<t_2$, $m<S$:
--   $$F(z) = \sum_{i<S}\ \sum_{j,k'<2N} c(i,j,k')\, z^i\, e^{(jx_1+k'x_2)z}.$$
--
--   **Proof sketch.** Write each equation, multiplied by a power of $D$, in the basis $\omega^h\omega_1^k$ with $k<d$, reducing modulo $Q$. That is a homogeneous integer linear system with roughly $48rd\,N^2S^2$ unknowns and $18rd\,N^2S^2$ equations. Siegel's lemma over $\mathbb{Z}$ (`Int.exists_ne_zero_int_vec_norm_le`) gives $q$. The monomials $\omega^\mu\omega_1^\nu$ are linearly independent, by minimality of $Q$ and transcendence of $\omega$, so some $c \ne 0$.
--
--   The paper uses algebraic integers of a number field; here all four exponentials lie in $\mathbb{Q}(\omega,\omega_1)$, so integers suffice. The hypotheses are satisfiable.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemma 4; C. L. Siegel's lemma as in S. Lang, Introduction to Transcendental Numbers, ch. I §2. Superseded: the statement omits the hypothesis that the four exponentials exp(x_i y_j) are algebraic. Without it the omega-degree of their powers is unbounded, and the height bound cannot hold as stated. Replaced by FourExp.auxiliary_function_alg, which carries that hypothesis and is Proved.

import Mathlib

namespace FourExp

theorem auxiliary_function
    (x₁ x₂ y₁ y₂ : ℂ) (ω ω₁ : ℂ) (hω : Transcendental ℚ ω) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic) (hQd : 0 < Q.natDegree)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0) (hE : ∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∃ M : ℕ, (M : ℝ) ≤ κ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ ∧
      ∃ q : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
        (∀ i j k' μ ν, |((q i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
        (∃ i j k', (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' ≠ 0) ∧
        (∀ i j k', ‖(fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k'‖ ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
        (∀ a b m : ℕ, a < ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ → m < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
          iteratedDeriv m (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0) := by
  sorry

end FourExp
