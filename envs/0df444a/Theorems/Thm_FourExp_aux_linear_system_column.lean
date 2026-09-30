-- Prove2me | Theorems.Thm_FourExp_aux_linear_system_column
-- name    : FourExp.aux_linear_system_column
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:40:56.736326+00:00
-- url     : https://prove2.me/theorems/81adeeff-9cb0-4c16-90d4-33965d5c8b45
-- title:
--   A sufficient integer linear system for the auxiliary function, from presentations whose degree in ω grows with T·a
-- statement:
--   Let $x_1, x_2, y_1, y_2, \omega, \omega_1 \in \mathbb{C}$ and $Q \in \mathbb{Z}[X][Y]$. For integers $q_{ijk\mu\nu}$ ($i < S$, $j, k < T$, $\mu < M$, $\nu < \deg_Y Q$) put $F_q(z) = \sum_{i,j,k}\big(\sum_{\mu,\nu} q_{ijk\mu\nu}\,\omega^{\mu}\omega_1^{\nu}\big) z^{i} e^{(jx_1 + kx_2)z}$, and suppose that the derivatives of $F_q$ have the reduced presentations in the conclusion of `FourExp.exists_iteratedDeriv_reduced_presentation_column`, with $X$-degrees at most $M + c(1+m+S+Ta)$. Then there is $\kappa_1 > 0$ such that for every large $N$, with
--
--   $$S = \lfloor N^{2}/\sqrt{\log N}\rfloor,\quad T = 2N,\quad t_1 = \lfloor N/\sqrt{\log N}\rfloor,\quad t_2 = \lfloor N\sqrt{\log N}\rfloor,$$
--
--   there are an integer $M$ with $0 < M \le \kappa_1 S$ and an integer matrix $B$ with $R$ rows, $2R \le ST^{2}M\deg_Y Q$, and entries at most $e^{\kappa_1 N^{2}\sqrt{\log N}}$, such that $Bq = 0$ implies $F_q^{(m)}(ay_1 + by_2) = 0$ for all $a < t_1$, $b < t_2$, $m < S$.
--
--   This is the equation count of Lemme 4 of Waldschmidt (1973), and `FourExp.aux_linear_system` with the presentation as its only hypothesis; the conclusion is the same. In the four exponentials case the $X$-degrees are at most $M + c(1+m+S)$. Here $a < t_1$ gives $Ta \le 2Nt_1 \le 2S$, so $M = (5c+1)S$ in place of $(3c+1)S$ still leaves at least twice as many unknowns as equations.
-- source:
--   The equation count in the proof of Lemme 4 of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202 (pp. 197–198). Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- The auxiliary linear system of Waldschmidt's argument, from a reduced presentation of the
derivatives whose `X`-degrees grow with `T a`.

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, `S = ⌊N² / √(log N)⌋`, `t₁ = ⌊N / √(log N)⌋` and
`t₂ = ⌊N √(log N)⌋`. The unknowns are integers `q_{ijkμν}` with `i < S`, `j, k < 2N`, `μ < M`,
`ν < deg Q`, and `F_q(z) = ∑ (∑_{μ,ν} q_{ijkμν} ω^μ ω₁^ν) z^i e^((j x₁ + k x₂) z)`. The hypothesis
`hpres` is the conclusion of `FourExp.exists_iteratedDeriv_reduced_presentation_column`: the
derivatives have reduced presentations with `X`-degrees at most `M + c (1 + m + S + T a)`.

Then there are, for large `N`, an `M ≤ κ₁ S` and an integer system with at most half as many
equations as unknowns and coefficients at most `e^(κ₁ N² √(log N))`, whose solutions make
`F_q⁽ᵐ⁾(a y₁ + b y₂)` vanish for `a < t₁`, `b < t₂`, `m < S`. The conclusion is that of
`FourExp.aux_linear_system`. Since `a < t₁` gives `T a ≤ 2 N t₁ ≤ 2 S`, `M = (5 c + 1) S` leaves
room for the `X`-degrees. -/
theorem aux_linear_system_column
    (x₁ x₂ y₁ y₂ : ℂ) (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ))
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
