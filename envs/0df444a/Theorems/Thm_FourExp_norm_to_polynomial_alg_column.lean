-- Prove2me | Theorems.Thm_FourExp_norm_to_polynomial_alg_column
-- name    : FourExp.norm_to_polynomial_alg_column
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:41:02.413412+00:00
-- url     : https://prove2.me/theorems/731b223a-6992-4c87-a410-1129b4aad5f9
-- title:
--   Norms of small values give small integer polynomials, from presentations whose degree in ω grows with T·a
-- statement:
--   Let $x_1, x_2, y_1, y_2, \omega, \omega_1 \in \mathbb{C}$, and let $Q \in \mathbb{Z}[X][Y]$ be monic in $Y$ with $Q(\omega, \omega_1) = 0$ and minimal there: no non-zero $A \in \mathbb{Z}[X][Y]$ of smaller $Y$-degree vanishes at $(\omega, \omega_1)$. Suppose that the derivatives of the auxiliary function $F_q$ have the reduced presentations in the conclusion of `FourExp.exists_iteratedDeriv_reduced_presentation_column`, and let $\kappa, \kappa' > 0$. Then there is $k > 0$ such that for every $C$ and every large $N$ the following holds, with
--
--   $$S = \lfloor N^{2}/\sqrt{\log N}\rfloor,\quad t_1 = \lfloor N/\sqrt{\log N}\rfloor,\quad t_2 = \lfloor N\sqrt{\log N}\rfloor.$$
--
--   Let $M \le \kappa S$ and let the integers $q_{ijk\mu\nu}$ ($i < S$, $j, k < 2N$, $\mu < M$, $\nu < \deg_Y Q$) satisfy $|q_{ijk\mu\nu}| \le e^{\kappa N^{2}\sqrt{\log N}}$. If $a < 14t_1$, $b < 14t_2$, $s < S/2$ and
--
--   $$0 < |F_q^{(s)}(ay_1 + by_2)| \le e^{-N^{4}\sqrt{\log N}/\kappa'},$$
--
--   then there is a non-zero $P \in \mathbb{Z}[X]$ with coefficients at most $e^{kN^{2}\sqrt{\log N}}$, degree at most $kN^{2}/\sqrt{\log N}$ and $|P(\omega)| < e^{-Ck^{2}N^{4}}$.
--
--   This is Lemme 7 of Waldschmidt (1973). `FourExp.norm_to_polynomial_alg` assumes all four $e^{x_iy_j}$ algebraic and derives the presentation from them; here the presentation is the hypothesis, and the conclusion is the same. $P$ is the norm of the reduced value down to $\mathbb{Q}(\omega)$, from `FourExp.exists_int_norm`. Since $a < 14t_1$ gives $2Na \le 28N^{2}/\sqrt{\log N}$, the $X$-degree $M + c(1+s+S+2Na)$ stays $O(N^{2}/\sqrt{\log N})$, and only the constant $k$ grows.
-- source:
--   M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Lemme 7 (pp. 200–201). Formal proof: Diaz modulus mission, 30 September 2026 (C. Perassi).

import Mathlib

namespace FourExp

/-- A small non-zero derivative gives an integer polynomial that is small at `ω`, from a reduced
presentation of the derivatives whose `X`-degrees grow with `T a`.

Write `φ(P) = P(ω, ω₁)` for `P ∈ ℤ[X][Y]`, with `Q ∈ ℤ[X][Y]` monic in `Y`, `φ(Q) = 0`, and no
non-zero `A` of smaller `Y`-degree with `φ(A) = 0`. The hypothesis `hpres` is the conclusion of
`FourExp.exists_iteratedDeriv_reduced_presentation_column`. Let the integers `q_{ijkμν}` satisfy
`|q| ≤ e^(κ N² √(log N))` with `μ < M ≤ κ S`. If `F_q⁽ˢ⁾(a y₁ + b y₂)` is non-zero and at most
`e^(-N⁴ √(log N) / κ')` on the 14-fold grid (`a < 14 t₁`, `b < 14 t₂`, `s < S/2`), then its norm
down to `ℚ(ω)` is an integer polynomial `P ≠ 0` of height at most `e^(k N² √(log N))` and degree at
most `k N² / √(log N)` with `|P(ω)| < e^(-C (k N² √(log N)) (k N² / √(log N)))`.

The conclusion is that of `FourExp.norm_to_polynomial_alg`. Since `a < 14 t₁` gives
`T a ≤ 28 N² / √(log N)`, the `X`-degree `M + c (1 + s + S + T a)` is still `O(N² / √(log N))`;
only the constant `k` grows. -/
theorem norm_to_polynomial_alg_column
    (x₁ x₂ y₁ y₂ : ℂ) (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)) (hQm : Q.Monic)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
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
              Polynomial.C (Polynomial.C (q i j k μ ν)) * R i j k μ ν))
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
