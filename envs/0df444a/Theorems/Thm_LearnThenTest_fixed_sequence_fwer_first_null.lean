-- Prove2me | Theorems.Thm_LearnThenTest_fixed_sequence_fwer_first_null
-- name    : LearnThenTest.fixed_sequence_fwer_first_null
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T00:12:07.699788+00:00
-- url     : https://prove2.me/theorems/0592e56f-8b53-40aa-ad0e-ff808f98847d
-- title:
--   Proposition 4 (as proved): the FWER of single-start fixed sequence testing is the probability of rejecting the first null
-- statement:
--   Consider fixed sequence testing (Algorithm 1) with a single initialization $\mathcal J=\{j_0\}$ and level $\delta\in(0,1)$, applied to p-values $p_1,\dots,p_N$ (random variables on one probability space). Let $J_0$ be the set of true nulls, and let $j^*$ be the first null in the sequence: $j^*\in J_0$, $j^*\ge j_0$, and no null lies in $[j_0,j^*)$. Then:
--
--   1. the procedure rejects a true null if and only if it rejects $\mathcal H_{j^*}$, so $\mathrm{FWER}=\mathbb P(j^*\in\hat\Lambda)$;
--   2. $\mathrm{FWER}\le\mathbb P(p_{j^*}\le\delta)$;
--   3. if $j^*=j_0$, then $\mathrm{FWER}=\mathbb P(p_{j^*}\le\delta)$.
--
--   **Formalization Note** The paper prints the equality $\mathrm{FWER}=\mathbb P(p_{j^*}\le\delta)$ without restriction. Its proof establishes items 1 and 2 only. The equality fails when a non-null before $j^*$ can be accepted. Example: $N=2$, $j_0=1$, $\mathcal H_1$ false with $p_1\equiv1$, and $\mathcal H_2$ true with $p_2$ uniform. Then $\mathrm{FWER}=0$, while $\mathbb P(p_2\le\delta)=\delta$. The statement therefore records what the proof establishes, together with the case $j^*=j_0$ in which the printed equality holds.
-- source:
--   Angelopoulos, Bates, Candès, Jordan and Lei, Learn then Test: Calibrating Predictive Algorithms to Achieve Risk Control, arXiv:2110.01052v5 (2022), Section 2.3.1, Algorithm 1 and Proposition 4, p. 5; proof in Appendix C, p. 22

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter

namespace LearnThenTest

theorem fixed_sequence_fwer_first_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) (p : Fin N → Ω → ℝ)
    (hp : ∀ j, Measurable (p j)) (j0 : Fin N) (J0 : Finset (Fin N)) (jstar : Fin N)
    (hjstar : jstar ∈ J0) (hj0 : j0 ≤ jstar) (hfirst : ∀ k ∈ J0, j0 ≤ k → jstar ≤ k) :
    fwer P (fixedSeq N δ {j0}) p J0 = P {ω | jstar ∈ fixedSeq N δ {j0} (fun i => p i ω)} ∧
    fwer P (fixedSeq N δ {j0}) p J0 ≤ P {ω | p jstar ω ≤ δ} ∧
    (jstar = j0 → fwer P (fixedSeq N δ {j0}) p J0 = P {ω | p jstar ω ≤ δ}) := by sorry

end LearnThenTest
