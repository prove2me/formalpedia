-- Prove2me | Theorems.Thm_OptAbstention_TLA_proposition_B_6
-- name    : OptAbstention.TLA.proposition_B_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:07:28.763206+00:00
-- url     : https://prove2.me/theorems/aa4c8d98-be98-4af2-8535-949c4a8be96f
-- title:
--   Proposition B.6: support functions of $K_R(U(S))$ and $K_R(D)$ agree up to $R\tau/2$
-- statement:
--   In the setting of Lemma B.2 ($\Omega$, a distribution $D$, $\tau>0$, $\delta\in(0,1)$, $k\ge1$, measurable $\psi$), let $S$ be $n$ i.i.d. samples from $D$ with $n\ge C\,k\,\mathbb E_{x\sim D}[\|\psi(x)\|_\infty^2]/(\tau\delta)^2$, $C$ universal. Then with probability at least $1-\delta/2$,
--   $$\sup_{R\ge1,\ q\in\mathbb R^k:\ \|q\|_1\le1}R^{-1}\big|H_{K_R(U(S))}(q)-H_{K_R(D)}(q)\big|\le\tau/2 .$$
--   Applied to two independent samples it gives Lemma B.2.
--
--   Differences from the source:
--   - encoding: sup_{R,q} R⁻¹|H₁(q) − H₂(q)| ≤ τ/2 → for every R ≥ 1 and ‖q‖₁ ≤ 1: H₁ ≤ H₂ + Rτ/2 and H₂ ≤ H₁ + Rτ/2 in EReal; reason: equivalent when both values are finite, which the hypotheses force
--   - encoding: |S| ≳ k E_D[‖ψ‖²_∞]/(τδ)² → n ≥ C·k·E/(τδ)² in [0,∞] with E a lower Lebesgue integral and C universal; reason: an infinite moment makes the hypothesis unsatisfiable, as in the source
--   - encoding: probability at least 1 − δ → the measure (outer measure) of the failure set is at most δ; reason: equivalent for measurable events, and never weaker
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 40, Proposition B.6

import Mathlib
import Definitions.Def_OptAbstention_TLA_CappedReweighting

open MeasureTheory

namespace OptAbstention.TLA

/-- Proposition B.6, p. 40 (setup of Lemma B.2): if `|S| ≳ k E_D[‖ψ‖_∞²]/(τδ)²`, then with
probability at least `1 − δ/2`, `R⁻¹ |H_{K_R(U(S))}(q) − H_{K_R(D)}(q)| ≤ τ/2` for every `R ≥ 1`
and `‖q‖₁ ≤ 1` (stated as the two one-sided bounds with `Rτ/2` in `EReal`). -/
theorem proposition_B_6 : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D] (τ δ : ℝ)
      (k : ℕ) (ψ : Ω → Fin k → ℝ), 0 < τ → 0 < δ → δ < 1 → 1 ≤ k → Measurable ψ →
      ∀ n : ℕ,
      ENNReal.ofReal C * k * (∫⁻ x, (‖ψ x‖₊ : ENNReal) ^ 2 ∂D) / ENNReal.ofReal ((τ * δ) ^ 2)
          ≤ (n : ENNReal) →
      (Measure.pi fun _ : Fin n => D)
        {S | ¬ ∀ R : ℝ, 1 ≤ R → ∀ q : Fin k → ℝ, l1norm q ≤ 1 →
          supportFn (KR (empMeasure S) ψ R) q ≤ supportFn (KR D ψ R) q + ((R * τ / 2 : ℝ) : EReal) ∧
          supportFn (KR D ψ R) q ≤ supportFn (KR (empMeasure S) ψ R) q + ((R * τ / 2 : ℝ) : EReal)}
        ≤ ENNReal.ofReal (δ / 2) := by sorry

end OptAbstention.TLA
