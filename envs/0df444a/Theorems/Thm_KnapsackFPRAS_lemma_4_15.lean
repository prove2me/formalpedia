-- Prove2me | Theorems.Thm_KnapsackFPRAS_lemma_4_15
-- name    : KnapsackFPRAS.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:39:37.733783+00:00
-- url     : https://prove2.me/theorems/dfa4a752-d9a8-4763-8147-b5590bf14d38
-- title:
--   Lemma 4.15 — random-shift rounding is unbiased with MGF $\le e^{t^2s^2/8}$, also conditionally
-- statement:
--   Let $s'>0$, let $J\ge1$ be an integer and $s=Js'$, and let $\alpha_s$ be the random-shift rounding of Eq. (23) with a shift $H$ uniform on $\{0,\dots,J-1\}$.
--
--   1. For every fixed input value $x=s'j$ with $j\in\mathbb Z$ and every real $t$,
--   $$
--   \mathbb E[\alpha_s(x)]=x,\qquad \mathbb E\bigl[e^{t(\alpha_s(x)-x)}\bigr]\le e^{t^2s^2/8}.
--   $$
--   2. The same bounds hold conditionally when $x$ depends only on earlier shifts: on a probability space, let $\mathcal G$ be a sub-σ-algebra, let $H$ be uniform on $\{0,\dots,J-1\}$ and independent of $\mathcal G$, and let $j$ be a $\mathcal G$-measurable integer; then almost surely
--   $$
--   \mathbb E[\alpha_s(x)-x\mid\mathcal G]=0,\qquad \mathbb E\bigl[e^{t(\alpha_s(x)-x)}\bigm|\mathcal G\bigr]\le e^{t^2s^2/8}.
--   $$
--
--   The rounding errors created at different nodes of the counting tree therefore form a sequence of conditionally centered, conditionally sub-Gaussian errors, which is the hypothesis of Corollary 2.3.
--
--   Differences from the source:
--   - generalization: J a power of two → any integer J ≥ 1; reason: the claim holds for every J ≥ 1 and specializes to powers of two
--   - reading: conditionally when x depends only on shifts used at earlier nodes → conditional on a sub-σ-algebra 𝒢 (the earlier shifts), with H uniform and independent of 𝒢 and j 𝒢-measurable, almost surely; reason: the shift of the current node is independent of the earlier shifts and x is a function of them
--   - encoding: E[α_s(x) | 𝒢] = x → E[α_s(x) − x | 𝒢] = 0; reason: the error is bounded by s, so this needs no integrability assumption on x; same content
--   - encoding: E over the uniform shift H → the average (1/J)∑_{H∈Fin J}; reason: same expectation
--   - encoding: the spacing s′ (implicitly positive) → s′ > 0; reason: a spacing is positive
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Lemma 4.15, p.27 (PDF p.28), with Eq. (23), p.26 (PDF p.27)

import Mathlib
import Definitions.Def_KnapsackFPRAS_shiftRound

set_option autoImplicit false

namespace KnapsackFPRAS

open MeasureTheory ProbabilityTheory

/-- **Lemma 4.15**, p.27. "For every fixed input value 𝑥 = 𝑠′𝑗 with 𝑗 ∈ ℤ, E[𝛼_𝑠(𝑥)] = 𝑥 and,
for every real 𝑡 ∈ ℝ, E[𝑒^{𝑡(𝛼_𝑠(𝑥)−𝑥)}] ≤ 𝑒^{𝑡²𝑠²/8}. The same bounds hold conditionally when
𝑥 depends only on shifts used at earlier nodes."

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Lemma 4.15, p.27 (PDF p.28), with `α_s` of Eq. (23), p.26.

**Formalization Note.** `s = J s′` with `s′ > 0` and any integer `J ≥ 1` (the page has `J` a
power of two). Part 1: the shift `H` is uniform on `{0, …, J − 1}`, so the expectations are
averages over `H : Fin J`. Part 2 (the conditional bounds): on a probability space, `𝒢` is the
σ-algebra of the earlier shifts, the current shift `H` is uniform on `Fin J` and independent of
`𝒢`, and the index `j` is `𝒢`-measurable; then `E[α_s(x) − x | 𝒢] = 0` and
`E[e^{t(α_s(x)−x)} | 𝒢] ≤ e^{t²s²/8}` almost surely. The first is stated for the error
`α_s(x) − x` (bounded by `s`, hence integrable), which is "`E[α_s(x) | 𝒢] = x`" without an
integrability condition on `x`. -/
theorem lemma_4_15 :
    (∀ (s' : ℝ), 0 < s' → ∀ (J : ℕ), 1 ≤ J → ∀ (j : ℤ) (t : ℝ),
      (1 / (J : ℝ)) * ∑ H : Fin J, shiftRound s' J H j = s' * j ∧
      (1 / (J : ℝ)) * ∑ H : Fin J, Real.exp (t * (shiftRound s' J H j - s' * j)) ≤
        Real.exp (t ^ 2 * ((J : ℝ) * s') ^ 2 / 8)) ∧
    (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝒢 : MeasurableSpace Ω), 𝒢 ≤ mΩ →
      ∀ (s' : ℝ), 0 < s' → ∀ (J : ℕ), 1 ≤ J →
      ∀ (H : Ω → Fin J), Measurable H → (∀ h : Fin J, μ.real (H ⁻¹' {h}) = 1 / (J : ℝ)) →
      Indep (MeasurableSpace.comap H inferInstance) 𝒢 μ →
      ∀ (j : Ω → ℤ), Measurable[𝒢] j → ∀ t : ℝ,
        μ[fun ω => shiftRound s' J (H ω) (j ω) - s' * j ω | 𝒢] =ᵐ[μ] 0 ∧
        μ[fun ω => Real.exp (t * (shiftRound s' J (H ω) (j ω) - s' * j ω)) | 𝒢] ≤ᵐ[μ]
          fun _ => Real.exp (t ^ 2 * ((J : ℝ) * s') ^ 2 / 8)) := by sorry

end KnapsackFPRAS
