-- Prove2me | Theorems.Thm_OptAbstention_TLA_fact_A_6
-- name    : OptAbstention.TLA.fact_A_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:07:25.539622+00:00
-- url     : https://prove2.me/theorems/cadb9089-f0c4-40c6-bcac-ebbcb05dd2bd
-- title:
--   Fact A.6: $\mathbb E\sup_{f\in\mathcal F}|\mathbb E_{U(S)}f-\mathbb E_Df|\lesssim\sqrt{V\,\mathbb E_D[F^2]/n}$ for a VC-subgraph class (as printed; see insight I5)
-- statement:
--   Let $D$ be a distribution on a set $\Omega$, $\mathcal F\subseteq\mathbb R^\Omega$ a pointwise measurable class of measurable functions with VC-subgraph dimension $V$, and $F:\Omega\to[0,\infty)$ an envelope, $|f|\le F$ for every $f\in\mathcal F$. There is a universal constant $C$ such that for every $n\ge1$
--   $$\mathbb E_{S\sim D^n}\Big[\sup_{f\in\mathcal F}\Big|\mathbb E_{x\sim U(S)}[f(x)]-\mathbb E_{x\sim D}[f(x)]\Big|\Big]\le C\sqrt{\frac{V\,\mathbb E_{x\sim D}[F(x)^2]}{n}} .$$
--   It is cited from van der Vaart and Wellner and is the uniform-convergence engine of Proposition B.6.
--
--   **Formalization Note.** The outer expectation is a lower Lebesgue integral in $[0,\infty]$ (the supremum is measurable under pointwise measurability), and the square root is the power $1/2$ in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: VC-subgraph dimension equal to V → VC-subgraph dimension at most V; reason: the right-hand side increases in V, so the source's case follows
--   - reading: F: X → [0,∞) any function with |f| ≤ F → F measurable; reason: E_D[F(x)²] is defined only for measurable F; for a general F the outer expectation equals that of a measurable envelope F* ≥ F, which is again an envelope
--   - encoding: E_{S∼D^n}[sup …] and sqrt(V E[F²]/n) → lower Lebesgue integral and ENNReal power 1/2, universal C fixed first; reason: same values when E[F²] < ∞
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 35, Fact A.6 with footnote 12

import Mathlib
import Definitions.Def_OptAbstention_TLA_CappedReweighting

open MeasureTheory

namespace OptAbstention.TLA

/-- Fact A.6, p. 35: for a pointwise measurable class `F` of measurable functions with
VC-subgraph dimension `V` and envelope `F_env`,
`E_{S∼D^n}[sup_{f∈F} |E_{U(S)} f − E_D f|] ≤ C √(V E_D[F_env²]/n)`, `C` universal. -/
theorem fact_A_6 : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
      (F : Set (Ω → ℝ)) (V : ℕ) (Fenv : Ω → ℝ),
      PointwiseMeasurableClass F → (∀ f ∈ F, Measurable f) → vcSubgraphDim F ≤ V →
      Measurable Fenv → (∀ x, 0 ≤ Fenv x) → (∀ f ∈ F, ∀ x, |f x| ≤ Fenv x) →
      ∀ n : ℕ, 1 ≤ n →
      ∫⁻ S, (⨆ f ∈ F, ENNReal.ofReal |(∑ i, f (S i)) / n - ∫ x, f x ∂D|)
          ∂(Measure.pi fun _ : Fin n => D) ≤
        ENNReal.ofReal C *
          ((V : ENNReal) * (∫⁻ x, ENNReal.ofReal (Fenv x ^ 2) ∂D) / n) ^ (1 / 2 : ℝ) := by sorry

end OptAbstention.TLA
