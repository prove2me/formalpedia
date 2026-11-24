-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Trees_Supplement_theorem2_printed_argmin_false
-- name    : OfflinePolicyLearning.Trees.Supplement.theorem2_printed_argmin_false
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T08:13:18.188819+00:00
-- url     : https://prove2.me/theorems/5c2415d5-0684-4b09-afb4-d2122bcaa112
-- title:
--   Theorem 2, p. 20 (corrected: the printed oracle bound for π̃ ∈ arg min Q̃ is false — counterexample)
-- statement:
--   In the potential-outcome model of the paper, a draw consists of features $X$, potential rewards $(Y(a_1),\dots,Y(a_d))$ and a logged action $A$, with propensities $e_a(x)=\mathbf P[A=a\mid X=x]$ and mean rewards $\mu_a(x)=\mathbf E[Y(a)\mid X=x]$. The oracle score of a draw is $\Gamma=\frac{Y(A)-\mu_A(X)}{e_A(X)}A+(\mu_{a_1}(X),\dots,\mu_{a_d}(X))$, the oracle value estimate of a policy is $\tilde Q(\pi)=\frac1n\sum_i\langle\pi(X_i),\Gamma_i\rangle$, the regret is $R(\pi)=\sup_{\pi'\in\Pi}Q(\pi')-Q(\pi)$ with $Q(\pi)=\mathbf E[Y(\pi(X))]$, and $V^*=\sup_{\pi_a,\pi_b\in\Pi}\mathbf E[\langle\Gamma,\pi_a(X)-\pi_b(X)\rangle^2]$.
--
--   Theorem 2 of the paper asserts: under Assumption 1 (unconfoundedness, overlap $e_a(x)\ge\eta>0$, bounded rewards) and Assumption 3, if $\tilde\pi\in\arg\min_{\pi\in\Pi}\tilde Q(\pi)$, then for any $\delta>0$, with probability at least $1-2\delta$,
--   $$R(\tilde\pi)\le\Big(54.4\sqrt2\,\kappa(\Pi)+435.2+\sqrt{2\log\tfrac1\delta}\Big)\sqrt{\frac{V^*}{n}}+o\Big(\frac1{\sqrt n}\Big).$$
--
--   The statement is: **this claim is false.** There is a model and a nonempty class of measurable policies satisfying Assumptions 1 and 3, a selection of empirical minimizers $\tilde\pi_n$ and a $\delta>0$ such that no sequence $r_n$ with $\sqrt n\,r_n\to0$ makes the displayed bound hold with probability at least $1-2\delta$ for every $n\ge1$.
--
--   For instance: one feature point, $d=2$, deterministic rewards $Y(a_1)=1$, $Y(a_2)=0$, uniform logging and the two constant policies. The oracle score is $\Gamma=(1,0)$ for every draw, so the unique minimizer of $\tilde Q$ always plays $a_2$ and has regret $1$, while the right side tends to $0$; for $\delta=1/4$ the bound fails with probability one for all large $n$.
--
--   The paper defines $\tilde\pi=\arg\max_{\pi\in\Pi}\tilde Q(\pi)$ in §4 (p. 14), and the first inequality of its proof (16) requires a maximizer, so "arg min" is a misprint for "arg max". The corrected maximizer statement is not posed here: it rests on the upper-bound form of Theorem 1 (see that item), and its second constant should read $435.2\sqrt2=54.4\sqrt2\cdot8$ according to (13) and (15).
--
--   **Formalization Note** Actions are `Fin d`, policies deterministic maps into `Fin d`, and the model is the published `OfflinePolicyLearning.Regret.Model`, whose law builds unconfoundedness in. The negated claim quantifies over feature types in `Type`, nonempty classes of measurable policies, an overlap constant $\eta>0$, a bound on the rewards for every feature value, Assumption 3 in the form "the covering number is finite and at most $C\exp(D\varepsilon^{-\omega})$", every selection of empirical minimizers, and $o(1/\sqrt n)$ as a deterministic sequence $r_n$ (allowed to depend on $\delta$) with $\sqrt n\,r_n\to0$, the bound required at every $n\ge1$. The extra regularity in the negated claim only makes the negation stronger.
--
--   Differences from the source:
--   - correction: for π̃ ∈ arg min Q̃, R(π̃) ≤ (54.4√2κ + 435.2 + √(2 log(1/δ)))√(V*/n) + o(1/√n) with probability ≥ 1 − 2δ → the negation of that claim (a counterexample exists); reason: with deterministic rewards (1,0), uniform logging and two constant policies, the minimizer of Q̃ has regret 1 for every n while the bound tends to 0
--   - encoding: Π any policy class and the paper's randomized-policy setting → nonempty classes of measurable deterministic policies X → Fin d in the negated claim; reason: the paper's proofs use deterministic one-hot policies (endnote 3, p. 45), and restricting the universally quantified claim strengthens its negation
--   - reading: "o(1/√n)" inside a probability statement → a deterministic sequence r with √n·r n → 0, chosen after δ, the bound holding at every n ≥ 1; reason: the most permissive reading of the printed claim, so its negation covers every reading
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 20, Theorem 2 and its proof (16); p. 14, §4 (π̃ = arg max Q̃); p. 9, Assumption 1; p. 14, Assumption 3; p. 10, Definition 3; p. 18, Remark 6

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory Filter Topology
open OfflinePolicyLearning.Regret

namespace OfflinePolicyLearning.Trees.Supplement

/-- Theorem 2, p. 20, as printed — for `π̃ ∈ arg min_{π∈Π} Q̃(π)` and any `δ > 0`, with
probability at least `1 − 2δ`,
`R(π̃) ≤ (54.4√2κ(Π) + 435.2 + √(2 log(1/δ)))√(V*/n) + o(1/√n)` under Assumptions 1 and 3 —
is false. The negated claim reads `o(1/√n)` as a deterministic sequence `r` with `√n·r n → 0`,
allowed to depend on `δ`, and adds that the policies are measurable. -/
theorem theorem2_printed_argmin_false :
    ¬ ∀ (X : Type) [MeasurableSpace X] (d : ℕ) (M : Model X d) (Pol : Set (X → Fin d)),
        Pol.Nonempty → (∀ π ∈ Pol, Measurable π) →
        (∃ η : ℝ, 0 < η ∧ ∀ x a, η ≤ M.e x a) →
        (∃ B : ℝ, ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B) →
        (∃ C D ω : ℝ, 0 < C ∧ 0 < D ∧ 0 < ω ∧ ω < 1 / 2 ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            hammingCoverNum ε Pol ≠ ⊤ ∧
            ((hammingCoverNum ε Pol).toNat : ℝ) ≤ C * Real.exp (D * (1 / ε) ^ ω)) →
        ∀ πt : (n : ℕ) → (Fin n → Draw X d) → X → Fin d,
          (∀ n D, πt n D ∈ Pol) →
          (∀ n D, ∀ π ∈ Pol, M.Qtilde D (πt n D) ≤ M.Qtilde D π) →
          ∀ δ : ℝ, 0 < δ → ∃ r : ℕ → ℝ, Tendsto (fun n : ℕ => Real.sqrt n * r n) atTop (𝓝 0) ∧
            ∀ n : ℕ, 1 ≤ n →
              ENNReal.ofReal (1 - 2 * δ) ≤ M.sample n {D | M.regret Pol (πt n D) ≤
                (54.4 * Real.sqrt 2 * (entropyIntegral Pol).toReal + 435.2 +
                    Real.sqrt (2 * Real.log (1 / δ))) * Real.sqrt (M.Vstar Pol / n) + r n} := by sorry

end OfflinePolicyLearning.Trees.Supplement
