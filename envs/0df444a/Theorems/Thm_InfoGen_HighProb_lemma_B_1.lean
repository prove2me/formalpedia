-- Prove2me | Theorems.Thm_InfoGen_HighProb_lemma_B_1
-- name    : InfoGen.HighProb.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:08.420098+00:00
-- url     : https://prove2.me/theorems/2bdf93ed-0e8e-45a0-95de-0e1c8f2b45bc
-- title:
--   Lemma B.1, p. 11 — m independent parallel copies of P_{W|S} with I(Λ_W(S);W) ≤ ε give I(Λ_W(S₁),…,Λ_W(S_m);W^m) ≤ mε
-- statement:
--   Let $\mathsf W$ be a measurable hypothesis space, $\mathsf Z$ an instance space with a probability measure $\mu$, $\ell : \mathsf W\times\mathsf Z\to\mathbb R_+$ a jointly measurable loss, and $P_{W|S}$ a learning algorithm (a Markov kernel from datasets $s \in \mathsf Z^n$ to $\mathsf W$). Write $\Lambda_{\mathsf W}(s) = (L_s(w))_{w\in\mathsf W}$ for the vector of empirical risks.
--
--   Consider the parallel execution of $m$ independent copies of $P_{W|S}$ on independent datasets: for $t = 1,\dots,m$, an independent copy of $P_{W|S}$ takes $S_t \sim \mu^{\otimes n}$ as input and outputs $W_t$, so that the pairs $(S_t, W_t)$ are i.i.d. with law $\mu^{\otimes n}\otimes P_{W|S}$. Let $\varepsilon \ge 0$. If $I(\Lambda_{\mathsf W}(S); W) \le \varepsilon$, then
--   $$I\big(\Lambda_{\mathsf W}(S_1),\dots,\Lambda_{\mathsf W}(S_m);\, W^m\big) \le m\varepsilon,$$
--   where $W^m = (W_1, \dots, W_m)$.
--
--   This is the first step of the "monitor technique" proof of Theorem 3: running the algorithm $m$ times independently costs at most $m$ times its information budget.
--
--   **Formalization Note.** The copies are indexed by `Fin m`. This tensorization statement holds for arbitrary measurable $\mathsf W$; the countability correction needed for the deviation bounds is not needed here. Joint measurability of $\ell$ is added so that $\Lambda_{\mathsf W}(S)$ is a random variable. $\varepsilon \ge 0$ is the paper's implicit convention (a mutual information is nonnegative).
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, Lemma B.1, p. 11

import Mathlib
import Definitions.Def_InfoGen_HighProb_Setting

open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal

namespace InfoGen.HighProb

theorem lemma_B_1 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (m : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : lambdaInfo ℓ μ κ ≤ ENNReal.ofReal ε) :
    InfoGen.Expected.mutualInfo ((parallelLaw μ κ m).map
        (fun p => ((fun t => empRiskVec ℓ (p t).1), (fun t => (p t).2)))) ≤
      ENNReal.ofReal (m * ε) := by sorry

end InfoGen.HighProb
