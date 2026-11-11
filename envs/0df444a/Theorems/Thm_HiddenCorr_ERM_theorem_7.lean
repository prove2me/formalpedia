-- Prove2me | Theorems.Thm_HiddenCorr_ERM_theorem_7
-- name    : HiddenCorr.ERM.theorem_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:35:12.860202+00:00
-- url     : https://prove2.me/theorems/9e9f698b-40ca-4ba4-b9c9-74d2ed4c0df8
-- title:
--   Theorem 7 — uniform bilinear Hanson–Wright inequality for dependent pairs, in expectation and with high probability
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $k\ge1$ and let $(X_1,V_1),\dots,(X_n,V_n)$ be independent pairs, where $X_i$ takes values in $\mathcal X$, $V_i\in\mathbb R^k$, $\mathbb EV_i=0$ and $\|V_i\|_2\le B_V$ almost surely; within a pair, $X_i$ and $V_i$ may be arbitrarily dependent. Let $F$ be a nonempty class of functions $f:\mathcal X\to\mathbb R^k$ with $\mathbb Ef(X_i)=0$ for every $f\in F$ and $i\in[n]$, and $\sup_{f\in F}\|f(X_i)\|_2\le B_F$ almost surely for every $i$, where $B_F,B_V>0$. For every deterministic $A\in\mathbb R^{n\times n}$, writing
--   $$\Delta_f=\sum_{i,j=1}^nA_{ij}\langle f(X_i),V_j\rangle-\sum_{i=1}^nA_{ii}\,\mathbb E\langle f(X_i),V_i\rangle,$$
--   (i) $\mathbb E\sup_{f\in F}|\Delta_f|\le C B_V\|A\|_F\,\mathbb E\hat{\mathfrak R}^{\mathrm{vec}}_X(F)$ (Eq. (28)), and (ii) for every $\delta\in(0,1/e)$, with probability at least $1-\delta$,
--   $$\sup_{f\in F}|\Delta_f|\le CB_V\|A\|_F\Big(\hat{\mathfrak R}^{\mathrm{vec}}_X(F)\sqrt{\log(1/\delta)}+B_F\log(1/\delta)\Big)\qquad\text{(Eq. (29))}.$$
--
--   Classical Hanson–Wright inequalities need independent coordinates; here the two members of a pair may be dependent, which is exactly the situation of covariance estimation along a hidden matching. The bound is uniform over a class and dimension-free in $k$.
--
--   Differences from the source:
--   - reading: footnote 1 (p. 13): all functions, learning rules and suprema over function classes are measurable → the relevant functions are Measurable and the class is pointwise measurable (countable dense subclass in the pointwise sense: published IsPointwiseMeasurableClass, or its vector version IsPointwiseMeasurableClassV); reason: standard reading of the measurability convention; it makes every supremum in the statement equal to a countable one
--   - encoding: E_ε over independent Rademacher signs, conditional on the sample; complexities possibly infinite → uniform average over all sign vectors (finite sum / 2^n); R̂_X, R̂^vec_X valued in [0, ∞] (ℝ≥0∞); reason: same quantity; ℝ≥0∞ keeps an unbounded class's +∞ value
--   - encoding: real-valued bounds and expectations of suprema → both sides in ℝ≥0∞ (ENNReal.ofReal of the nonnegative real terms, lower Lebesgue integral ∫⁻ for expectations of suprema); reason: the supremum and the complexity may be +∞; all terms are nonnegative, so nothing changes for finite values
--   - encoding: with probability at least 1 − δ, … → the measure (outer measure) of the set of samples on which the claim fails is ≤ ENNReal.ofReal δ; reason: avoids requiring the failure event to be measurable; equivalent when it is measurable
--   - encoding: log, natural logarithm; δ ∈ (0, 1/e) → Real.log; 0 < δ ∧ δ < Real.exp (-1); reason: same
--   - encoding: independent pairs (Xᵢ, Vᵢ); E Vᵢ = 0; E f(Xᵢ) = 0; ‖A‖_F → iIndepFun of i ↦ (Xᵢ, Vᵢ) with measurable Xᵢ, Vᵢ; Bochner means ∫ Vᵢ = 0, ∫ f(Xᵢ) = 0; ‖A‖_F = √(∑ᵢⱼ Aᵢⱼ²); reason: same assumptions; the bounded measurable integrands are integrable
-- source:
--   Chen, Gentile, Kaplan, Koren, Supervised Learning with Hidden Correspondences, STOC 2027 submission (manuscript sha256 d0029978…), p. 22, Theorem 7, Eqs. (28)–(29) (proof pp. 58–59, App. C.2)

import Mathlib
import Definitions.Def_HiddenCorr_ERM_Complexity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe u v

namespace HiddenCorr.ERM

/-- **Theorem 7** (uniform bilinear Hanson–Wright inequality), p. 22. There is an absolute constant
`C > 0` such that: let `k ≥ 1` and let `(X₁, V₁), …, (Xₙ, Vₙ)` be independent pairs, `Xᵢ` in `X`,
`Vᵢ ∈ ℝ^k`, `E Vᵢ = 0`, `‖Vᵢ‖₂ ≤ B_V` almost surely (within a pair, `Xᵢ` and `Vᵢ` may be dependent).
Let `F` be a nonempty (pointwise measurable) class of measurable `f : X → ℝ^k` with `E f(Xᵢ) = 0`
for all `f ∈ F`, `i ∈ [n]`, and `sup_{f ∈ F} ‖f(Xᵢ)‖₂ ≤ B_F` almost surely, `B_F, B_V > 0`. Then for
every deterministic `A ∈ ℝ^{n×n}`:
(i) `E sup_{f ∈ F} |∑_{i,j} A_{ij}⟨f(Xᵢ), Vⱼ⟩ − ∑ᵢ A_{ii} E⟨f(Xᵢ), Vᵢ⟩| ≤ C B_V ‖A‖_F E R̂^vec_X(F)`;
(ii) for every `δ ∈ (0, 1/e)`, with probability at least `1 − δ`,
`sup_{f ∈ F} |…| ≤ C B_V ‖A‖_F (R̂^vec_X(F) √(log(1/δ)) + B_F log(1/δ))`. -/
theorem theorem_7 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {𝒳 : Type v} [MeasurableSpace 𝒳] (k n : ℕ), 1 ≤ k →
        ∀ (X : Fin n → Ω → 𝒳) (V : Fin n → Ω → EuclideanSpace ℝ (Fin k)),
        (∀ i, Measurable (X i)) → (∀ i, Measurable (V i)) →
        iIndepFun (fun i ω => (X i ω, V i ω)) P →
        (∀ i, ∫ ω, V i ω ∂P = 0) →
        ∀ BF BV : ℝ, 0 < BF → 0 < BV →
        (∀ i, ∀ᵐ ω ∂P, ‖V i ω‖ ≤ BV) →
        ∀ F : Set (𝒳 → EuclideanSpace ℝ (Fin k)), F.Nonempty → (∀ f ∈ F, Measurable f) →
        IsPointwiseMeasurableClassV F →
        (∀ f ∈ F, ∀ i, ∫ ω, f (X i ω) ∂P = 0) →
        (∀ i, ∀ᵐ ω ∂P, ∀ f ∈ F, ‖f (X i ω)‖ ≤ BF) →
        ∀ A : Matrix (Fin n) (Fin n) ℝ,
          let dev : (𝒳 → EuclideanSpace ℝ (Fin k)) → Ω → ℝ := fun f ω =>
            ∑ i, ∑ j, A i j * inner ℝ (f (X i ω)) (V j ω) -
              ∑ i, A i i * ∫ ω', inner ℝ (f (X i ω')) (V i ω') ∂P
          let normA : ℝ := Real.sqrt (∑ i, ∑ j, A i j ^ 2)
          (∫⁻ ω, (⨆ f ∈ F, ENNReal.ofReal |dev f ω|) ∂P ≤
              ENNReal.ofReal (C * BV * normA) * ∫⁻ ω, radVec (fun i => X i ω) F ∂P) ∧
          (∀ δ : ℝ, 0 < δ → δ < Real.exp (-1) →
            P {ω | ∃ f ∈ F,
                ENNReal.ofReal (C * BV * normA) *
                    (radVec (fun i => X i ω) F * ENNReal.ofReal (Real.sqrt (Real.log (1 / δ))) +
                      ENNReal.ofReal (BF * Real.log (1 / δ))) <
                  ENNReal.ofReal |dev f ω|} ≤ ENNReal.ofReal δ) := by sorry

end HiddenCorr.ERM
