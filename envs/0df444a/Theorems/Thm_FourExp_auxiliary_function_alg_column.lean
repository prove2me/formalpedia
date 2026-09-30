-- Prove2me | Theorems.Thm_FourExp_auxiliary_function_alg_column
-- name    : FourExp.auxiliary_function_alg_column
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:40:52.913773+00:00
-- url     : https://prove2.me/theorems/1d0ddadc-b140-4ea9-8c4f-b0cb29332ceb
-- title:
--   Siegel's lemma builds the auxiliary function from presentations whose degree in ω grows with T·a
-- statement:
--   Let $x_1, x_2, y_1, y_2, \omega, \omega_1 \in \mathbb{C}$, and let $Q \in \mathbb{Z}[X][Y]$ have $Y$-degree $d \ge 1$ and be minimal at $(\omega, \omega_1)$: no non-zero $A \in \mathbb{Z}[X][Y]$ of $Y$-degree less than $d$ vanishes there. Suppose that the derivatives of the auxiliary function have the reduced presentations in the conclusion of `FourExp.exists_iteratedDeriv_reduced_presentation_column`. Then there is $\kappa > 0$ such that for every large $N$, with $S = \lfloor N^{2}/\sqrt{\log N}\rfloor$, $t_1 = \lfloor N/\sqrt{\log N}\rfloor$ and $t_2 = \lfloor N\sqrt{\log N}\rfloor$, there are $M \le \kappa S$ and integers $q_{ijk\mu\nu}$ ($i < S$, $j, k < 2N$, $\mu < M$, $\nu < d$) with $|q_{ijk\mu\nu}| \le e^{\kappa N^{2}\sqrt{\log N}}$ such that the numbers $c_{ijk} = \sum_{\mu,\nu} q_{ijk\mu\nu}\,\omega^{\mu}\omega_1^{\nu}$ are not all zero, satisfy $|c_{ijk}| \le e^{\kappa N^{2}\sqrt{\log N}}$, and give a function
--
--   $$F(z) = \sum_{i<S}\ \sum_{j,k<2N} c_{ijk}\, z^{i} e^{(jx_1 + kx_2)z}$$
--
--   with $F^{(m)}(ay_1 + by_2) = 0$ for all $a < t_1$, $b < t_2$, $m < S$.
--
--   This is Lemme 4 of Waldschmidt (1973). `FourExp.auxiliary_function_alg` assumes all four $e^{x_iy_j}$ algebraic and derives the presentation from them; here the presentation is the hypothesis, and the conclusion is the same. The proof is `FourExp.aux_linear_system_column` followed by Siegel's lemma in the form `FourExp.siegel_aux`, where the minimality of $Q$ makes some $c_{ijk}$ non-zero.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemme 4 (pp. 197–198), with Siegel's lemma, Lemme 1 there (p. 194), after S. Lang, Introduction to Transcendental Numbers (1966), ch. I §2. Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- Siegel's auxiliary function of Waldschmidt's argument, from a reduced presentation of the
derivatives whose `X`-degrees grow with `T a`.

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, with `Q ∈ ℤ[X][Y]` of positive `Y`-degree such that no
non-zero `A` of smaller `Y`-degree has `φ(A) = 0`. The hypothesis `hpres` is the conclusion of
`FourExp.exists_iteratedDeriv_reduced_presentation_column`. Then there are `κ > 0` and, for large
`N`, integers `q_{ijkμν}`, not all giving zero coefficients, with `|q| ≤ e^(κ N² √(log N))` and
`μ < M ≤ κ S`, such that `F(z) = ∑ c_{ijk} z^i e^((j x₁ + k x₂) z)` with
`c_{ijk} = ∑ q_{ijkμν} ω^μ ω₁^ν` vanishes to order `S` at the points `a y₁ + b y₂`, `a < t₁`,
`b < t₂`. The conclusion is that of `FourExp.auxiliary_function_alg`; the proof is
`FourExp.aux_linear_system_column` followed by `FourExp.siegel_aux`. -/
theorem auxiliary_function_alg_column
    (x₁ x₂ y₁ y₂ : ℂ) (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)) (hQd : 0 < Q.natDegree)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (hpres : ∃ c : ℕ, ∀ S T M a b m : ℕ, ∃ Λ : ℂ, Λ ≠ 0 ∧
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
              Polynomial.C (Polynomial.C (q i j k μ ν)) * R i j k μ ν)) :
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
