-- Prove2me | Theorems.Thm_OptHedgeGames_Supplement_theorem_6_23
-- name    : OptHedgeGames.Supplement.theorem_6_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:23:20.984906+00:00
-- url     : https://prove2.me/theorems/a1ca86d3-5f43-44f8-9101-a2f817ba1534
-- title:
--   Theorem 6.23 — the cascade has an exact period-$M$ orbit, $M=2^{k+1}$, with block $j$ rotating at frequency $2^{j-1}$, attracting the uniform start
-- statement:
--   Let $k\ge1$, $n\ge8k+1$ and $M=2^{k+1}$, and let $0<\eta\le1/100$ with $\eta M\ge16\pi n$. Put $\lambda=e^{2\pi i/M}$, $K_j=2^{j-1}$ and $\Lambda_j=\lambda^{K_j}$. Then there are $a_0>0$, constants $K,C<\infty$, $\rho\in[0,1)$ and $c_j\ne0$ ($2\le j\le k$), depending only on $n,\eta,M,k$, such that for every $a\in(0,a_0)$ there are $\mu,\delta\in\mathbb C$ with the following properties.
--   1. $|\delta|\le Ka$.
--   2. All utilities of the cascade lie in $[-\tfrac12,\tfrac12]$, for every pair of actions.
--   3. The recurrence (64) has an orbit $s^*_t=(z^*_{j,t},\varrho^*_{j,t})_{j\le k}$, $s^*_{t+1}=\Phi_{\mu,\delta}(s^*_t)$, of exact period $M$, with
--   $$
--   |z^*_{1,t}-\delta-a\lambda^t|\le Ka^2,\qquad |z^*_{j,t}-c_ja^{K_j}\Lambda_j^t|\le Ka^{K_j+1}\quad(2\le j\le k),
--   $$
--   for all $t\ge0$.
--   4. The trajectory $s_t$ of (64) from the uniform start $s_0=0$ satisfies $\|s_t-s^*_t\|\le Ca\rho^t$ for all $t\ge0$, in the Euclidean norm of $\mathbb C^{2k}$.
--
--   Block $j$ oscillates at $2^{j-1}$ times the base frequency, so the last block has period four; this fast oscillation is what forces linear regret on the observer in Theorem 3.6.
--
--   **Formalization Note** Blocks are 0-based in Lean (block `j` is the paper's $j+1$), so $K_{j+1}=2^j$ and the clause for $2\le j\le k$ reads `1 ≤ j.val`; the value of $c$ at the first block is unused. With $\eta\le1/100$ and $n\ge8k+1$ the hypothesis $\eta M\ge16\pi n$ requires $2^{k+1}\ge1600\pi(8k+1)$, so the statement has content only for $k\ge19$; this is the paper's own hypothesis set.
--
--   Differences from the source:
--   - reading: "for every sufficiently small $a$", "$\delta=O(a)$", the $O(\cdot)$ remainders, "constants $c_j\ne0$ that do not depend on $a$", "some $C<\infty$ and $\rho<1$, independent of $t$ and of sufficiently small $a$" → $\exists a_0>0,\ K,\ C,\ \rho,\ c$ after $k,n,M,\eta$ and before $\forall a\in(0,a_0)$; reason: the paper's convention on p.27; one $K$ serves all $O(\cdot)$ bounds.
--   - encoding: $\rho<1$ → $0\le\rho<1$; reason: a negative $\rho$ serves only when the trajectory equals the orbit, where $\rho=0$ serves too.
--   - encoding: "orbit of exact period $M$; the remainders are $M$-periodic" → $s^*_{t+1}=\Phi(s^*_t)$, $s^*_{t+M}=s^*_t$, no period $0<p<M$, $t\in\mathbb N$; remainder periodicity not restated; reason: it follows from $s^*_{t+M}=s^*_t$ and $\lambda^M=\Lambda_j^M=1$.
--   - encoding: blocks $1,\dots,k$ and $\|\cdot\|$ on $\mathbb C^{2k}$ → `Fin k` (0-based) and the explicit Euclidean distance `cascDist`; reason: the same blocks and the norm fixed on p.27.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), Theorem 6.23, p.40; constants convention p.27

import Mathlib
import Definitions.Def_OptHedgeGames_Supplement_Cascade

namespace OptHedgeGames

namespace Supplement

/-- **Theorem 6.23 (The cascade).** Let `k ≥ 1`, `n ≥ 8k + 1` and `M = 2^{k+1}`, and suppose
`0 < η ≤ 1/100` and `ηM ≥ 16πn`. For every sufficiently small `a > 0` there are `µ, δ ∈ ℂ`, with
`δ = O(a)`, for which all utilities lie in `[−1/2, 1/2]` and (64) has an orbit
`s*ₜ = (z*_{j,t}, ϱ*_{j,t})_{j≤k}` of exact period `M` with `z*_{1,t} = δ + aλᵗ + O(a²)` and
`z*_{j,t} = c_j a^{K_j} Λ_jᵗ + O(a^{K_j+1})` (`2 ≤ j ≤ k`), where the constants `c_j ≠ 0` do not
depend on `a` and the remainders are `M`-periodic. The trajectory from the uniform start satisfies
`∥sₜ − s*ₜ∥ ≤ Caρᵗ` (`t ≥ 0`) for some `C < ∞` and `ρ < 1`, independent of `t` and of sufficiently
small `a`. Here `λ = e^{2πi/M}`, `K_j = 2^{j−1}` and `Λ_j = λ^{K_j}`
(Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), Theorem 6.23, p.40).

**Formalization Note** Blocks are `Fin k`, 0-based: block `j` is the paper's block `j + 1`, so
`K_{j+1} = 2^j` and the clause for `2 ≤ j ≤ k` reads `1 ≤ j.val`. The paper's convention (p.27):
`a₀`, the constants `K` of the `O(·)`s, `c_j`, `C` and `ρ` may depend on `n, η, M, k` but not on `t`
or on `a`, so they come before `∀ a`. The uniform start is `s₀ = 0`. `∥·∥` is the Euclidean norm on
`ℂ^{2k}` (`cascDist`). An orbit of exact period `M` is a sequence with `s*ₜ₊₁ = Φ_{µ,δ}(s*ₜ)`,
`s*ₜ₊ₘ = s*ₜ` and no smaller positive period. `ρ ≥ 0` is added, as in Theorem 6.2. The values of
`c_j` for the first block are not used. -/
theorem theorem_6_23 :
    ∀ (k n M : ℕ) (η : ℝ), 1 ≤ k → 8 * k + 1 ≤ n → M = 2 ^ (k + 1) → 0 < η → η ≤ 1 / 100 →
      16 * Real.pi * (n : ℝ) ≤ η * (M : ℝ) →
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ K C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
        ∃ c : Fin k → ℂ, (∀ j : Fin k, 1 ≤ j.val → c j ≠ 0) ∧
        ∀ a : ℝ, 0 < a → a < a₀ →
          ∃ μ δ : ℂ, ‖δ‖ ≤ K * a ∧
            (∀ τ σ : CascadeAction n k, cascU μ δ τ σ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) ∧
            ∃ sStar : ℕ → (Fin k → ℂ) × (Fin k → ℂ),
              (∀ t, sStar (t + 1) = cascStep n k η μ δ (sStar t)) ∧
              (∀ t, sStar (t + M) = sStar t) ∧
              (∀ p : ℕ, 0 < p → p < M → ∃ t, sStar (t + p) ≠ sStar t) ∧
              (∀ (j : Fin k) (t : ℕ), j.val = 0 →
                ‖(sStar t).1 j - δ - (a : ℂ) *
                  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ)) ^ t‖ ≤ K * a ^ 2) ∧
              (∀ (j : Fin k) (t : ℕ), 1 ≤ j.val →
                ‖(sStar t).1 j - c j * (a : ℂ) ^ (2 ^ j.val) *
                  (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ)) ^ (2 ^ j.val)) ^ t‖ ≤
                  K * a ^ (2 ^ j.val + 1)) ∧
              (∀ t : ℕ, cascDist (cascTraj n k η μ δ t) (sStar t) ≤ C * a * ρ ^ t) := by sorry

end Supplement

end OptHedgeGames
