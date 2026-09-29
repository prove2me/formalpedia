-- Prove2me | Theorems.Thm_FourExp_siegel_aux
-- name    : FourExp.siegel_aux
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-17T10:21:02.724035+00:00
-- url     : https://prove2.me/theorems/b421c5b8-a7f6-4c18-a1c0-d45a9e8fb2c7
-- title:
--   Siegel's lemma for the auxiliary function, and why its coefficients are non-zero
-- statement:
--   **Solving the system.** Let $\omega, \omega_1 \in \mathbb{C}$ and $Q \in \mathbb{Z}[X][Y]$ with $d = \deg_Y Q \ge 1$, such that no non-zero $A \in \mathbb{Z}[X][Y]$ with $\deg_Y A < d$ vanishes at $(\omega, \omega_1)$. Let $\kappa_1 > 0$. Then there is $\kappa \ge \kappa_1$ such that for every large $N$, with $S = \lfloor N^2/\sqrt{\log N}\rfloor$, every $0 < M \le \kappa_1 S$ and every $R \times U$ integer matrix $B$ with $U = S\,(2N)^2\,M\,d$, $2R \le U$ and entries at most $e^{\kappa_1N^2\sqrt{\log N}}$, there is an integer vector $q$ with $Bq = 0$ such that:
--   - every $|q| \le e^{\kappa N^2\sqrt{\log N}}$;
--   - $c(i,j,k') = \sum_{\mu<M,\nu<d} q(i,j,k',\mu,\nu)\,\omega^\mu\omega_1^\nu$ is non-zero for some $(i,j,k')$;
--   - every $|c(i,j,k')| \le e^{\kappa N^2\sqrt{\log N}}$.
--
--   **Proof plan.** Siegel's lemma over $\mathbb{Z}$ (`Int.exists_ne_zero_int_vec_norm_le`) with $U \ge 2R$ gives $q \ne 0$ with $|q| \le U\max|B|$, and $\log U = O(\log N)$. If $q(i,j,k',\cdot,\cdot) \ne 0$, then $\sum_{\mu,\nu} q\,X^\mu Y^\nu$ is non-zero with $\deg_Y < d$, so by minimality $c(i,j,k') \ne 0$. The bound on $c$ absorbs $\log(Md) + M\log\max(1,|\omega|) + d\log\max(1,|\omega_1|) = O(S)$.
--
--   **Role.** The linear-algebra half of `FourExp.auxiliary_function_alg`. The hypotheses are satisfiable.
-- source:
--   C. L. Siegel's lemma, as in S. Lang, Introduction to Transcendental Numbers, ch. I §2; used as in M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemma 4.

import Mathlib

namespace FourExp

theorem siegel_aux
    (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)) (hQd : 0 < Q.natDegree)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (κ₁ : ℝ) (hκ₁ : 0 < κ₁) :
    ∃ κ : ℝ, κ₁ ≤ κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∀ M : ℕ, 0 < M → (M : ℝ) ≤ κ₁ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → ∀ R : ℕ, 2 * R ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ * (2 * N) * (2 * N) * M * Q.natDegree →
      ∀ B : Fin R → Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
        (∀ e i j k' μ ν, |((B e i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ₁ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) →
        ∃ q : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
          (∀ e, ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N), ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, B e i j k' μ ν * q i j k' μ ν = 0) ∧
          (∀ i j k' μ ν, |((q i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
          (∃ i j k', (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' ≠ 0) ∧
          (∀ i j k', ‖(fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k'‖ ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) := by
  sorry

end FourExp
