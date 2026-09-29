-- Prove2me | Theorems.Thm_FourExp_transcendence_criterion
-- name    : FourExp.transcendence_criterion
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-14T19:01:27.132229+00:00
-- url     : https://prove2.me/theorems/65f053a5-33bf-46c5-95a8-ac81974255c5
-- title:
--   A Gel'fond-type transcendence criterion
-- statement:
--   **A transcendence criterion of Gel'fond type.**
--
--   Let $\alpha \in \mathbb{C}$ and $\varepsilon > 0$. Let $\sigma_1, \sigma_2 : \mathbb{R} \to \mathbb{R}$ be strictly increasing with $\sigma_i(x) \to \infty$, and let $a_1, a_2 \ge 1$ be constants such that, for every $x > 0$,
--   $$\sigma_2(x) \le \sigma_1(x), \qquad \sigma_i(x+1) \le a_i\,\sigma_i(x) \quad (i = 1, 2).$$
--   Suppose that for every integer $N$ beyond some $N_0$ there is a non-zero $P_N \in \mathbb{Z}[X]$ with
--   $$\log H(P_N) \le \sigma_1(N), \qquad \deg P_N \le \sigma_2(N), \qquad |P_N(\alpha)| < \exp\bigl(-C\,\sigma_1(N)\,\sigma_2(N)\bigr),$$
--   where $H$ is the maximum absolute value of the coefficients and $C = \max\{10 + \varepsilon,\ (4+\varepsilon)\,a_1 a_2\}$. Then $\alpha$ is algebraic.
--
--   **What it is for.** In Gel'fond's method, transcendence of one number is proved by building integer polynomials that are too small at it. This criterion turns such a sequence into a contradiction when the number is transcendental. It is the tool that lets the Brownawell–Waldschmidt proof of four exponentials in transcendence degree one reduce to one transcendental generator $\omega$ of the field, and so it feeds `DiazModulus.four_exponentials_trdeg_one`.
--
--   **Formalization.** "$\log H \le \sigma_1(N)$" is written as a bound $|\text{coeff}| \le e^{\sigma_1(N)}$ on every coefficient. The paper also allows $a_i$ to depend on $x$; the constant case is the one its applications use (Remark 2), and it avoids a supremum over an unbounded family. The paper's second conclusion, that $P_N(\alpha) = 0$ for large $N$, is omitted.
-- source:
--   M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §3, Lemme fondamental (a refinement of Gel'fond's criterion, Transcendental and Algebraic Numbers, 1952, Ch. III §4 Lemma VII). Stated here with constant a_i, as in Remark 2 of that paper.

import Mathlib

open Filter Topology

namespace FourExp

theorem transcendence_criterion
    (α : ℂ) (ε : ℝ) (hε : 0 < ε)
    (σ₁ σ₂ : ℝ → ℝ) (hσ₁ : StrictMono σ₁) (hσ₂ : StrictMono σ₂)
    (hσ₁t : Tendsto σ₁ atTop atTop) (hσ₂t : Tendsto σ₂ atTop atTop)
    (a₁ a₂ : ℝ) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    (h₂₁ : ∀ x : ℝ, 0 < x → σ₂ x ≤ σ₁ x)
    (hgrowth₁ : ∀ x : ℝ, 0 < x → σ₁ (x + 1) ≤ a₁ * σ₁ x)
    (hgrowth₂ : ∀ x : ℝ, 0 < x → σ₂ (x + 1) ≤ a₂ * σ₂ x)
    (N₀ : ℕ) (P : ℕ → Polynomial ℤ)
    (hP_ne : ∀ N : ℕ, N₀ < N → P N ≠ 0)
    (hP_height : ∀ N : ℕ, N₀ < N → ∀ i : ℕ, |((P N).coeff i : ℝ)| ≤ Real.exp (σ₁ N))
    (hP_deg : ∀ N : ℕ, N₀ < N → ((P N).natDegree : ℝ) ≤ σ₂ N)
    (hP_small : ∀ N : ℕ, N₀ < N →
      ‖Polynomial.aeval α (P N)‖ <
        Real.exp (-(max (10 + ε) ((4 + ε) * (a₁ * a₂)) * σ₁ N * σ₂ N))) :
    IsAlgebraic ℚ α := by
  sorry

end FourExp
