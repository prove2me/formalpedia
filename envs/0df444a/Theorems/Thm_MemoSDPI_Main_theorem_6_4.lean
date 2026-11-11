-- Prove2me | Theorems.Thm_MemoSDPI_Main_theorem_6_4
-- name    : MemoSDPI.Main.theorem_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:42:36.323784+00:00
-- url     : https://prove2.me/theorems/249273b2-630e-40b0-bbcb-fa74f3ee9a84
-- title:
--   Theorem 6.4 — agreement test: a ρ-replicable A yields A′ on 2n samples with success 1 − β − ρ and I(A′(S̃); S̃) ≤ min{3/e, 2ρ + ρ log(1/ρ)}
-- statement:
--   Let $\mathcal P$ be a family of distributions and, for each $D \in \mathcal P$, let $\mathrm{Good}(D)$ be a set of successful outputs. Let $A$ be a $\rho$-replicable algorithm on $\mathcal P$ that uses $n$ samples and satisfies $\Pr[A(S;R) \in \mathrm{Good}(D)] \ge 1-\beta$ for every $D \in \mathcal P$, where $S \sim D^n$ and the seed $R$ are independent. Then there is an algorithm $A'$ using $2n$ samples such that for every $D \in \mathcal P$ and $\tilde S \sim D^{2n}$,
--   $$
--   \Pr[A'(\tilde S) \in \mathrm{Good}(D)] \;\ge\; 1 - \beta - \rho
--   \quad\text{and}\quad
--   I(A'(\tilde S); \tilde S) \;\le\; \min\Big\{\frac{3}{e},\ 2\rho + \rho\log\frac{1}{\rho}\Big\}.
--   $$
--   In particular, $\mathrm{mem}_{2n}(A', P) \le \min\{3/e, 2\rho + \rho\log(1/\rho)\}$ for every average-case problem $P = (P_\theta)_{\theta\sim\Psi}$ with $P_\theta \in \mathcal P$ for every $\theta$ in the support of $\Psi$.
--
--   The algorithm $A'$ may not depend on $D$: it is chosen before $D$. The statement is formalized as printed; it places no restriction on $\rho$ (see the mission's insight: for $\rho > e^2$ the bound is negative while every algorithm is $\rho$-replicable). Theorem 7.4 uses it with $\rho \le 1/100$.
--
--   **Formalization Note** $A'$ has output type $Y \oplus \mathrm{Unit}$, with `Sum.inr ()` the abstention symbol $\bot$ and $A'(\tilde S) \in \mathrm{Good}(D)$ read as `A′ = Sum.inl y` for some $y\in\mathrm{Good}(D)$. The real upper bound on an information $I \in [0,\infty]$ is stated as "$I \ne \infty$ and $I \le$ bound in $\mathbb R$", which keeps the printed meaning for every $\rho$. Replicability is the mission's `IsReplicableOn`; probabilities are measures of the success sets under sample law $\otimes$ seed law. The average-case clause quantifies over every parameter type, prior and family $\theta\mapsto P_\theta$.
--
--   Differences from the source:
--   - encoding: A′ outputs a value of A or a new symbol ⊥ → A′ : RandAlg X (Y ⊕ Unit) (2n), ⊥ = Sum.inr (), success = Sum.inl y with y ∈ Good(D); reason: Option carries no σ-algebra in Mathlib; Y ⊕ Unit is Y with one added point
--   - encoding: I(A′(S̃); S̃) ≤ b with b real → I ≠ ∞ ∧ I.toReal ≤ b; reason: an information in [0, ∞] is at most a real b exactly when it is finite and its real value is ≤ b; ENNReal.ofReal b would clamp a negative b to 0 and change the printed statement
--   - generalization: P_θ ∈ 𝒫 for every θ in the support of Ψ → P_θ ∈ 𝒫 for Ψ-almost every θ; reason: the support is not defined on a general measurable space; where it is (second countable spaces) the complement of the support is Ψ-null, so the printed hypothesis implies the Lean one and the Lean statement specializes to the source
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 26, Theorem 6.4

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsReplicableAt
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_MemoSDPI_Main_Memorization
import Definitions.Def_MemoSDPI_Main_IsReplicableOn

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 26, Theorem 6.4 (as printed; see finding I1): from a `ρ`-replicable `A` on a family
`F` that succeeds with probability `1 − β` on every `D ∈ F` there is an algorithm `A′` on `2n`
samples (output `Sum.inr ()` = the abstention symbol ⊥) with success probability `≥ 1 − β − ρ` and
`I(A′(S̃); S̃) ≤ min{3/e, 2ρ + ρ log(1/ρ)}` for every `D ∈ F`, and hence
`mem_{2n}(A′, P) ≤ min{3/e, 2ρ + ρ log(1/ρ)}` for every average-case problem over `F`. -/
theorem theorem_6_4 {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (F : Set (ProbabilityMeasure X)) (Good : ProbabilityMeasure X → Set Y) (ρ β : ℝ)
    (A : DPVerify.RandAlg X Y n) (hrep : IsReplicableOn A F ρ)
    (hsucc : ∀ D ∈ F, ENNReal.ofReal (1 - β) ≤
      ((Measure.pi fun _ : Fin n => (D : Measure X)).prod A.P) {q | A.run q.1 q.2 ∈ Good D}) :
    ∃ A' : DPVerify.RandAlg X (Y ⊕ Unit) (2 * n),
      (∀ D ∈ F,
        ENNReal.ofReal (1 - β - ρ) ≤
            ((Measure.pi fun _ : Fin (2 * n) => (D : Measure X)).prod A'.P)
              {q | ∃ y ∈ Good D, A'.run q.1 q.2 = Sum.inl y} ∧
          memD A' (D : Measure X) ≠ ∞ ∧
          (memD A' (D : Measure X)).toReal ≤
            min (3 / Real.exp 1) (2 * ρ + ρ * Real.log (1 / ρ))) ∧
      (∀ (Θ : Type) [MeasurableSpace Θ] (Ψ : Measure Θ) [IsProbabilityMeasure Ψ]
          (Pθ : Θ → ProbabilityMeasure X), (∀ᵐ θ ∂Ψ, Pθ θ ∈ F) →
        memAvg A' Ψ (fun θ => (Pθ θ : Measure X)) ≠ ∞ ∧
          (memAvg A' Ψ (fun θ => (Pθ θ : Measure X))).toReal ≤
            min (3 / Real.exp 1) (2 * ρ + ρ * Real.log (1 / ρ))) := by sorry

end MemoSDPI.Main
