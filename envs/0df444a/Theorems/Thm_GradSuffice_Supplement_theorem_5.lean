-- Prove2me | Theorems.Thm_GradSuffice_Supplement_theorem_5
-- name    : GradSuffice.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:29:28.348351+00:00
-- url     : https://prove2.me/theorems/30acc97b-0e15-4d1f-ae6b-5ef615539981
-- title:
--   Theorem 5, p.16 — $\mathcal R^{(s)}_m(W;\bar\xi)\ge a$ yields a $B^\star$-valued tree of depth $\lfloor ma^2/(128^2C^2\log m)\rfloor$ shattered by $W$ at margin $>a/1024$
-- statement:
--   Let $B$ be the unit ball of a real Banach space $X$ and let $W\subseteq B$ be a symmetric ($w\in W\Rightarrow -w\in W$), nonempty, convex set. There is a universal constant $C\ge1$ such that the following holds. Fix $0<a\le1$ and an integer $m\ge(32/a)^2$, and suppose some $B^\star$-valued adaptive sequence $\bar\xi=(\xi_1,\dots,\xi_m)$ satisfies
--   $$\mathcal R^{(s)}_m(W;\bar\xi)=\frac1m\,\mathbb E_\sigma\Big[\rho_W\Big(\sum_{i=1}^m\sigma_i\,\xi_i(\sigma_{<i})\Big)\Big]\ge a .\tag{9}$$
--   Then there is a $B^\star$-valued adaptive sequence $\tilde\xi=(\tilde\xi_1,\dots,\tilde\xi_n)$ of length
--   $$n:=\Big\lfloor\frac{m\,a^2}{128^2\,C^2\log m}\Big\rfloor$$
--   such that for every assignment $\sigma_1,\dots,\sigma_n\in\{-1,1\}$ there is $w_\sigma\in W$ with
--   $$\sigma_i\,w_\sigma\cdot\tilde\xi_i(\sigma_{<i})>\frac{a}{1024}\qquad\text{for every } i\le n.\tag{10}$$
--
--   In the non-dual setting, non-vanishing sequential Rademacher complexity thus produces shattered trees of arbitrary depth at small positive margins, which together with Theorem 8 obstructs optimization.
--
--   **Formalization Note** Signs are Booleans with `true` $\mapsto+1$ and positions are 0-based; $\sigma_{<i}$ is the prefix of the first $i$ signs. The logarithm is natural, and $m\ge(32/a)^2\ge1024$ makes $\log m>0$.
--
--   Differences from the source:
--   - encoding: C ≥ 1 is a universal constant → ∃ C ≥ 1 chosen before the space X, W, a and m; reason: quantifier form of "universal"
--   - encoding: an adaptive sequence ξ̄ (p.5: ξᵢ : {−1,1}^{i−1} → B⋆) → ξ : NondualOpt.Tree (StrongDual ℝ X) m with IsDualValued ξ; reason: adaptive sequences are B⋆-valued by the definition of p.5 and §6.1 (1-Lipschitz objectives)
--   - encoding: a (real Banach) space X, with no restriction on its size → X : Type (the lowest universe); reason: the constants are quantified before X, so X ranges over one fixed universe; universe-level convention, as in the base mission's theorem_sec2_i and theorem_3
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 5, p.16

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix
import Definitions.Def_GradSuffice_signR
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_Supplement_seqRadW

namespace GradSuffice.Supplement

/-- **Theorem 5 (non-dual Rademacher complexity yields a deep shattered tree).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 5, p.16:
"Let `W ⊆ B` be a symmetric, non empty convex set. Fix `0 < a ≤ 1` and an integer `m ≥ (32/a)²`.
Suppose there exists an adaptive sequence `ξ̄ = (ξ₁, …, ξₘ)` such that
`R⁽ˢ⁾ₘ(W; ξ̄) = (1/m) E_σ[ρ_W(∑ᵢ σᵢ ξᵢ(σ<ᵢ))] ≥ a` (9). Then there exists an adaptive sequence
`ξ̃ = (ξ̃₁, …, ξ̃ₙ)` with values in `B⋆` and length `n := ⌊m a² / (128² C² log m)⌋`, where `C ≥ 1` is a
universal constant, such that, for every assignment `σ₁, …, σₙ ∈ {−1, 1}`, there exists `w_σ ∈ W`
such that `σᵢ w_σ · ξ̃ᵢ(σ<ᵢ) > a/1024` for every `i ≤ n` (10)."

**Formalization Note.** `C ≥ 1` is chosen before the space, `W`, `a` and `m`. Adaptive sequences
are `B⋆`-valued (p.5), so the hypothesis' `ξ̄` is `IsDualValued`. "Symmetric" is `w ∈ W → −w ∈ W`.
`n` is the floor `Nat.floor`, `log` is natural (`m ≥ (32/a)² ≥ 1024`, so `log m > 0`). Signs are
`Bool` (`true ↦ +1`), positions 0-based; (10) is strict. -/
theorem theorem_5 :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (W : Set X),
        W ⊆ Metric.closedBall (0 : X) 1 → (∀ w ∈ W, -w ∈ W) → W.Nonempty → Convex ℝ W →
        ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ m : ℕ, (32 / a) ^ 2 ≤ (m : ℝ) →
        ∀ ξ : NondualOpt.Tree (StrongDual ℝ X) m, IsDualValued ξ → a ≤ seqRadW W ξ →
        ∃ ζ : NondualOpt.Tree (StrongDual ℝ X)
            (Nat.floor ((m : ℝ) * a ^ 2 / (128 ^ 2 * C ^ 2 * Real.log m))),
          IsDualValued ζ ∧
          ∀ σ : Fin (Nat.floor ((m : ℝ) * a ^ 2 / (128 ^ 2 * C ^ 2 * Real.log m))) → Bool,
            ∃ w ∈ W, ∀ i, a / 1024 < signR (σ i) * ζ i (NondualOpt.histPrefix σ i) w := by sorry

end GradSuffice.Supplement
