-- Prove2me | Theorems.Thm_MemoSDPI_Main_eq_2_1
-- name    : MemoSDPI.Main.eq_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:42:42.669181+00:00
-- url     : https://prove2.me/theorems/07df59f2-4ab0-496f-97a1-aa830bb86c9f
-- title:
--   Eq. (2.1) — excess memorization equals I(U; S | θ), and I(U; S) = I(U; θ) + mem_n(A, P)
-- statement:
--   Let $P = (P_\theta)_{\theta\sim\Psi}$ be an average-case problem: a prior $\Psi$ on a parameter space $\Theta$ and a measurable family of data distributions $P_\theta$ on $X$; draw $\theta\sim\Psi$ and then $S = (X_1,\dots,X_n)$ with records independent from $P_\theta$. Let $A$ be an algorithm with output space $Y$ whose seed is independent of $(\theta,S)$, and $U = A(S)$.
--   Excess memorization is $\mathrm{mem}_n(A,P) = \mathbb E_{\theta\sim\Psi}[\mathrm{mem}_n(A,P_\theta)]$ with $\mathrm{mem}_n(A, D) = I(A(S);S)$ for $S\sim D^n$. Then
--   $$
--   \mathrm{mem}_n(A, P) \;=\; I(U; S \mid \theta) \;=\; I(U; S) - I(U; \theta),
--   $$
--   the last equality by the chain rule and the conditional independence of $U$ and $\theta$ given $S$. The identity shows that only the information about the sample beyond the information about the parameter counts as memorization.
--
--   **Formalization Note** $I(U;S\mid\theta)$ is the published `ThompsonTutorial.InfoRatio.condMutualInfo` under the joint law of $(\theta, S, \text{seed})$; it is defined through regular conditional distributions, which requires $X$ and $Y$ standard Borel and nonempty. The second equality is stated additively in $[0,\infty]$. The family is assumed measurable, and the joint law is assumed finite (an instance argument needed to form the conditional information; it holds for every measurable family).
--
--   Differences from the source:
--   - encoding: mem_n(A, P) = I(U; S) − I(U; θ) → I(U; S) = I(U; θ) + mem_n(A, P) in ℝ≥0∞; reason: truncated subtraction in ℝ≥0∞ would be junk; the additive form is the chain-rule identity the equality expresses and is equivalent whenever I(U; θ) < ∞
--   - encoding: every data space X and output space Y → X and Y standard Borel and nonempty; reason: the published conditional mutual information is built from regular conditional distributions (condDistrib), which need standard Borel nonempty targets; every space of the paper ({0,1}^m, ℝ^d, finite sets) is standard Borel
--   - encoding: an average-case problem (P_θ) with θ ∼ Ψ → Ψ a probability measure, P : Θ → Measure X with each P θ a probability measure, Measurable P, and an instance that the joint law is finite; reason: drawing θ and then S ∼ P_θ^n presupposes a measurable family (a Markov kernel); the finiteness instance holds for every such family and only lets the conditional information be formed
--   - encoding: an algorithm A with randomness independent of (θ, S) → A : DPVerify.RandAlg X Y n with seed law A.P, joint law (θ, S) ⊗ seed; reason: the seed carries all internal randomness; same algorithms
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 9, eq. (2.1)

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_MemoSDPI_Main_Memorization

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 9, eq. (2.1): the excess memorization of `A` on the average-case problem
`P = (P_θ)_{θ∼Ψ}` equals `I(U; S | θ)`, and `I(U; S) = I(U; θ) + mem_n(A, P)`, where
`U = A(S)`. -/
theorem eq_2_1 {Θ X Y : Type} [MeasurableSpace Θ] [MeasurableSpace X] [StandardBorelSpace X]
    [Nonempty X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] {n : ℕ}
    (Ψ : Measure Θ) [IsProbabilityMeasure Ψ] (P : Θ → Measure X)
    [∀ θ, IsProbabilityMeasure (P θ)] (hP : Measurable P) (A : DPVerify.RandAlg X Y n)
    [IsFiniteMeasure (algJointLaw A Ψ P)] :
    memAvg A Ψ P =
        ThompsonTutorial.InfoRatio.condMutualInfo (algJointLaw A Ψ P)
          (fun q => A.run q.1.2 q.2) (fun q => q.1.2) (fun q => q.1.1) ∧
      infoSample A Ψ P = infoParam A Ψ P + memAvg A Ψ P := by sorry

end MemoSDPI.Main
