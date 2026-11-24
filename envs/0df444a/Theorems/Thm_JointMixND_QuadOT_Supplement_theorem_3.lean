-- Prove2me | Theorems.Thm_JointMixND_QuadOT_Supplement_theorem_3
-- name    : JointMixND.QuadOT.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:12:43.520821+00:00
-- url     : https://prove2.me/theorems/526f397e-9e1f-4f73-8c69-c4d0aa9f10e9
-- title:
--   Theorem 3, p. 8 — a random vector with finitely many values is a joint mix iff it is a finite linear combination of binary multinomial random vectors
-- statement:
--   Let $\mathbf X=(X_1,\dots,X_n)$ be a random vector on a probability space $(\Omega,\mathcal F,\mu)$ that takes values in a finite set. Then $\mathbf X$ is a joint mix ($\sum_iX_i$ almost surely constant) if and only if there are $m\in\mathbb N$, real coefficients $c_1,\dots,c_m$ and binary multinomial random vectors $\mathbf Y_1,\dots,\mathbf Y_m$ on $\Omega$ such that
--
--   $$\mathbf X=\sum_{k=1}^mc_k\mathbf Y_k\quad\text{almost surely}.$$
--
--   A binary multinomial vector takes values in $\{0,1\}^n$ with exactly one coordinate equal to $1$. The theorem generalizes Wang (2015, Theorem 2), which decomposes joint mixes with nonnegative integer values as sums of binary multinomial vectors.
--
--   **Formalization Note** $\mathbf X$ is measurable with finite range. The coefficients are arbitrary reals, possibly negative, and the vectors $\mathbf Y_k$ live on the same space as $\mathbf X$. Binary multinomial vectors satisfy their constraints almost surely, and the representation holds almost surely. The joint-mix property is the published `IsJointMix` applied to the law of $\mathbf X$.
--
--   Differences from the source:
--   - reading: X is represented as a finite linear combination of binary multinomial random vectors; binary multinomial vectors take values in {0,1}ⁿ with Σ Y_i = 1 → X = Σ_k c_k Y_k almost surely, with each Y_k measurable on the same space and in {0,1}ⁿ with Σ_i Y_k,i = 1 almost surely; reason: the joint-mix property is almost sure; the vectors built in the proof on pp. 25–26 satisfy their constraints wherever Σ X_i = c
--   - generalization: vectors of positive dimension n → n : ℕ, including n = 0; reason: at n = 0 the empty vector is a joint mix and is represented by the empty linear combination m = 0; all positive-dimensional source instances are retained
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 8, Theorem 3 (proof pp. 25–26)

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic
import Definitions.Def_JointMixND_QuadOT_Supplement_Dependence

open MeasureTheory ProbabilityTheory

namespace JointMixND.QuadOT.Supplement

theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Ω → Fin n → ℝ) (hX : Measurable X) (hfin : (Set.range X).Finite) :
    IsJointMix (μ.map X) ↔
      ∃ (m : ℕ) (c : Fin m → ℝ) (Y : Fin m → Ω → Fin n → ℝ),
        (∀ k, IsBinaryMultinomial μ (Y k)) ∧ X =ᵐ[μ] fun ω => ∑ k, c k • Y k ω := by sorry

end JointMixND.QuadOT.Supplement
