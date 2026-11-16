-- Prove2me | Theorems.Thm_OptHedgeGames_Supplement_theorem_6_2
-- name    : OptHedgeGames.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:22:38.687295+00:00
-- url     : https://prove2.me/theorems/8a13a5e1-b3d7-4e6e-89ae-43c430b02e9a
-- title:
--   Theorem 6.2 — an oscillating block has an exact period-$M$ orbit $z^*_t=\delta+a\lambda^t+O(a^2)$ attracting the uniform start
-- statement:
--   Let $n\ge9$, let $M\ge4$ be divisible by four, and let $0<\eta\le1/100$ with $\eta M\ge16\pi n$; put $\lambda=e^{2\pi i/M}$. Then there are $a_0>0$, constants $K,C<\infty$ and $\rho\in[0,1)$, depending only on $n,\eta,M$, such that for every $a\in(0,a_0)$ there are $\mu,\delta\in\mathbb C$ with the following properties.
--   1. $|\delta|\le Ka$.
--   2. The utility table (47) of the oscillating block takes values in $[-\tfrac12,\tfrac12]$ for every pair of actions.
--   3. The recurrence (49) has an orbit $s^*_t=(z^*_t,\varrho^*_t)$, $s^*_{t+1}=\Phi_{\mu,\delta}(s^*_t)$, of exact period $M$, with
--   $$
--   |z^*_t-\delta-a\lambda^t|\le Ka^2\qquad(t\ge0).
--   $$
--   4. The trajectory $(z_t,\varrho_t)$ of (49) from $(0,0)$ satisfies
--   $$
--   |z_t-z^*_t|+|\varrho_t-\varrho^*_t|\le Ca\rho^t\qquad(t\ge0).
--   $$
--
--   The block is the first stage of the paper's three-player construction: two players running Optimistic Hedge on these utilities follow the recurrence (Lemma 6.1) and settle into a cycle of period $M$.
--
--   **Formalization Note** With $\eta\le1/100$ the hypothesis $\eta M\ge16\pi n$ forces $M\ge1600\pi n$, so $M$ is large; this is the paper's own regime. The remainder $z^*_t-\delta-a\lambda^t$ is $M$-periodic because $s^*$ is and $\lambda^M=1$.
--
--   Differences from the source:
--   - reading: "for every sufficiently small $a$", "$\delta=O(a)$", "$O(a^2)$", "some $C<\infty$ and $\rho<1$, independent of $t$ and of sufficiently small $a$" → $\exists a_0>0,\ K,\ C,\ \rho$ after $n,M,\eta$ and before $\forall a\in(0,a_0)$; reason: the paper's convention on p.27 (constants depend on $n,\eta,M$ only, uniform in $t$ and small $a$); one $K$ serves both $O(\cdot)$ bounds.
--   - encoding: $\rho<1$ → $0\le\rho<1$; reason: a negative $\rho$ can serve only when the trajectory equals the orbit, where $\rho=0$ serves too, so no instance changes.
--   - encoding: "orbit of exact period $M$; the remainder is $M$-periodic" → $s^*_{t+1}=\Phi(s^*_t)$, $s^*_{t+M}=s^*_t$, no period $0<p<M$, indexed by $t\in\mathbb N$; the periodicity of the remainder is not restated; reason: it follows from $s^*_{t+M}=s^*_t$ and $\lambda^M=1$.
--   - encoding: actions → `Fin 8 ⊕ Fin (n - 8)` with coordinates `vtx` / $0$; reason: $n$ actions, eight active and $n-8$ neutral, as on p.25.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Theorem 6.2, pp.26–27; constants convention p.27

import Mathlib
import Definitions.Def_OptHedgeGames_Supplement_Block

namespace OptHedgeGames

namespace Supplement

/-- **Theorem 6.2 (An oscillating block).** Let `n ≥ 9`, let `M ≥ 4` be divisible by four, and
suppose `0 < η ≤ 1/100` and `ηM ≥ 16πn`. For every sufficiently small `a > 0` there are complex
parameters `µ, δ`, with `δ = O(a)`, for which the utility table (47) lies in `[−1/2, 1/2]` and the
recurrence (49) has an orbit `s*ₜ = (z*ₜ, ϱ*ₜ)` of exact period `M` with `z*ₜ = δ + aλᵗ + O(a²)`,
`λ = e^{2πi/M}`; the remainder is `M`-periodic. The trajectory from `(0, 0)` satisfies
`|zₜ − z*ₜ| + |ϱₜ − ϱ*ₜ| ≤ Caρᵗ` (`t ≥ 0`) for some `C < ∞` and `ρ < 1`, independent of `t` and of
sufficiently small `a`
(Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Theorem 6.2, pp.26–27).

**Formalization Note** The paper's convention (p.27): for fixed `n, η, M`, the threshold for `a`,
the constants of `O(a)` and `O(a²)`, `C` and `ρ` may depend on `n, η, M` but not on `t` or on `a`.
So `a₀, K, C, ρ` come after `n, M, η` and before `a`; one constant `K` serves both `O(·)`s. An orbit
of exact period `M` is a sequence with `s*ₜ₊₁ = Φ_{µ,δ}(s*ₜ)`, `s*ₜ₊ₘ = s*ₜ`, and no smaller positive
period; the remainder `z*ₜ − δ − aλᵗ` is then `M`-periodic automatically. `ρ ≥ 0` is added; a
negative `ρ` could only serve when `C a ρᵗ ≥ 0` for every `t`, which forces the trajectory to equal
the orbit, where `ρ = 0` serves too. -/
theorem theorem_6_2 :
    ∀ (n M : ℕ) (η : ℝ), 9 ≤ n → 4 ≤ M → 4 ∣ M → 0 < η → η ≤ 1 / 100 →
      16 * Real.pi * (n : ℝ) ≤ η * (M : ℝ) →
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ K C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
        ∀ a : ℝ, 0 < a → a < a₀ →
          ∃ μ δ : ℂ, ‖δ‖ ≤ K * a ∧
            (∀ τ σ : BlockAction n, blockU μ δ τ σ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) ∧
            ∃ sStar : ℕ → ℂ × ℂ,
              (∀ t, sStar (t + 1) = blockStep n η μ δ (sStar t)) ∧
              (∀ t, sStar (t + M) = sStar t) ∧
              (∀ p : ℕ, 0 < p → p < M → ∃ t, sStar (t + p) ≠ sStar t) ∧
              (∀ t : ℕ, ‖(sStar t).1 - δ - (a : ℂ) *
                  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ)) ^ t‖ ≤ K * a ^ 2) ∧
              (∀ t : ℕ, ‖(blockTraj n η μ δ t).1 - (sStar t).1‖ +
                  ‖(blockTraj n η μ δ t).2 - (sStar t).2‖ ≤ C * a * ρ ^ t) := by sorry

end Supplement

end OptHedgeGames
