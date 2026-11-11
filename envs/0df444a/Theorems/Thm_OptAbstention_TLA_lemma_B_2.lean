-- Prove2me | Theorems.Thm_OptAbstention_TLA_lemma_B_2
-- name    : OptAbstention.TLA.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:07:27.842208+00:00
-- url     : https://prove2.me/theorems/b7c0eb07-e5e6-4e81-86df-e7b6bdbf6bb9
-- title:
--   Lemma B.2: $K_R(U(X'))\subseteq K_R(U(X))+[-R\tau,R\tau]^k$ for all $R\ge1$ with probability $1-\delta$
-- statement:
--   Let $D$ be a distribution on a measurable space $\Omega$, $\tau>0$, $\delta\in(0,1)$, $k\ge1$ and $\psi:\Omega\to\mathbb R^k$ measurable. Let $X$ and $X'$ be independent i.i.d. samples from $D$ with $|X|,|X'|\ge C\,k\,\mathbb E_{x\sim D}[\|\psi(x)\|_\infty^2]/(\tau\delta)^2$, $C$ universal. Then with probability at least $1-\delta$, for every $R\ge1$,
--   $$K_R(U(X'))\subseteq K_R(U(X))+[-R\tau,R\tau]^k ,$$
--   where $+$ is the Minkowski sum. Specialized to the Chow features it is Corollary B.7.
--
--   Differences from the source:
--   - encoding: X and X′ multisets sampled i.i.d. from D → independent lists with law D^n ⊗ D^{n′}; reason: same law
--   - encoding: |X|, |X′| ≳ k E_D[‖ψ‖²_∞]/(τδ)² → n, n′ ≥ C·k·E/(τδ)² in [0,∞], C universal; reason: an infinite moment makes the hypothesis unsatisfiable, as in the source
--   - encoding: probability at least 1 − δ → the measure (outer measure) of the failure set is at most δ; reason: equivalent for measurable events, and never weaker
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 38, Lemma B.2

import Mathlib
import Definitions.Def_OptAbstention_TLA_CappedReweighting

open MeasureTheory
open scoped Pointwise

namespace OptAbstention.TLA

/-- Lemma B.2, p. 38: for independent i.i.d. samples `X, X′` from `D` with
`|X|, |X′| ≳ k E_D[‖ψ‖_∞²]/(τδ)²`, with probability at least `1 − δ`, for every `R ≥ 1`,
`K_R(U(X′)) ⊆ K_R(U(X)) + [−Rτ, Rτ]^k`. -/
theorem lemma_B_2 : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D] (τ δ : ℝ)
      (k : ℕ) (ψ : Ω → Fin k → ℝ), 0 < τ → 0 < δ → δ < 1 → 1 ≤ k → Measurable ψ →
      ∀ n n' : ℕ,
      ENNReal.ofReal C * k * (∫⁻ x, (‖ψ x‖₊ : ENNReal) ^ 2 ∂D) / ENNReal.ofReal ((τ * δ) ^ 2)
          ≤ (n : ENNReal) →
      ENNReal.ofReal C * k * (∫⁻ x, (‖ψ x‖₊ : ENNReal) ^ 2 ∂D) / ENNReal.ofReal ((τ * δ) ^ 2)
          ≤ (n' : ENNReal) →
      ((Measure.pi fun _ : Fin n => D).prod (Measure.pi fun _ : Fin n' => D))
        {q | ¬ ∀ R : ℝ, 1 ≤ R →
          KR (empMeasure q.2) ψ R ⊆ KR (empMeasure q.1) ψ R + boxSet k (R * τ)}
        ≤ ENNReal.ofReal δ := by sorry

end OptAbstention.TLA
