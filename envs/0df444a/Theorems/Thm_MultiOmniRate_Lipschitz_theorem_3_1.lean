-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_theorem_3_1
-- name    : MultiOmniRate.Lipschitz.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:23:30.521883+00:00
-- url     : https://prove2.me/theorems/745b9a86-ecca-4069-9804-ac806c8c5ace
-- title:
--   Theorem 3.1 — omniprediction for all Lipschitz losses from $C_K(\varepsilon^{-\max\{K-1,(K+2)/2\}}\log^2(2/\varepsilon)+\log(2N)/\varepsilon^2)$ samples
-- statement:
--   **Omniprediction for all Lipschitz losses.** For every $K\ge2$ there is a constant $C_K>0$, depending only on $K$, such that the following holds. Let $0<\varepsilon<1$, let $\mathcal X$ be any measurable space and $\mathcal H=\{h_1,\dots,h_N\}$, $N\ge1$, a class of measurable hypotheses $\mathcal X\to\Delta_K$, and let
--   $$n\ \ge\ C_K\Big(\varepsilon^{-\max\{K-1,(K+2)/2\}}\log^2(2/\varepsilon)+\frac{\log(2N)}{\varepsilon^2}\Big).$$
--   Then there is a learner $A$, a map from samples $S\in(\mathcal X\times\mathcal Y)^n$ to randomized predictors $\mathcal X\to\Delta(\Delta_K)$ that does not depend on the data distribution, such that:
--
--   1. for every distribution $\mathcal D$ on $\mathcal X\times\mathcal Y$,
--   $$\mathbb E_{S\sim\mathcal D^n}\big[\mathrm{OmniReg}_{\mathcal L_{\mathrm{Lip}},\mathcal H;\mathcal D}(A(S))\big]\le\varepsilon;$$
--   2. for every $0<\delta<1$, if moreover $n\ge C_K\big(\varepsilon^{-\max\{K-1,(K+2)/2\}}\log^2(2/\varepsilon)+\log(2N/\delta)/\varepsilon^2\big)$, then for every $\mathcal D$
--   $$\Pr_{S\sim\mathcal D^n}\big[\mathrm{OmniReg}_{\mathcal L_{\mathrm{Lip}},\mathcal H;\mathcal D}(A(S))>\varepsilon\big]\le\delta .$$
--
--   Here $\mathcal L_{\mathrm{Lip}}$ is the class of losses $\ell:\Delta_K\times\mathcal Y\to[-1,1]$ that are $1$-Lipschitz in the action for the Euclidean norm, and the bound holds for every choice of measurable best responses $\mathrm{BR}_\ell$. For $K=2$ this recovers the $1/\varepsilon^2$ rate of binary omniprediction up to logarithms; the first term grows as $\varepsilon^{-5/2}$ for $K=3$ and $\varepsilon^{-(K-1)}$ for $K\ge4$, matching the paper's lower bounds up to logarithmic factors.
--
--   **Formalization Note.** The learner is a function `(Fin n → X × Fin K) → Kernel X (Simplex K)` whose values are Markov kernels; it is chosen after $K$, $\varepsilon$, $\mathcal X$, $\mathcal H$ and $n$ and before $\mathcal D$ and $\delta$, so one learner serves both clauses.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - reading: "$\widetilde O_K(\varepsilon^{-\max\{K-1,(K+2)/2\}}+\log(2N)/\varepsilon^2)$ samples" → $n\ge C_K(\varepsilon^{-\max\{K-1,(K+2)/2\}}\log^2(2/\varepsilon)+\log(2N)/\varepsilon^2)$ with $C_K$ depending only on $K$; reason: the polylog factor the proof produces (Theorem 3.2 prints $\log^2(2/\varepsilon)$); a specific polylog is the stronger reading
--   - reading: "There is an algorithm that uses [that many] samples ... and returns a predictor" → for every $n$ above the bound there is a deterministic map $A$ from $n$-samples to randomized predictors (Markov kernels), not depending on $\mathcal D$ or $\delta$; reason: Theorem 3.2 says "whenever $n\ge\dots$"; Algorithm 1 is deterministic in training, its randomness lives in the output predictor
--   - reading: $\mathcal L_{\mathrm{Lip}}$ with "a fixed measurable best response" for each loss → `LLip K` contains every pair $(\ell,\mathrm{BR}_\ell)$ with $\mathrm{BR}_\ell$ measurable; OmniReg takes the supremum over all pairs; reason: the bound for all pairs is the bound for every choice of measurable best responses (the proof uses no property of the choice)
--   - encoding: $\mathbb E_S[\mathrm{OmniReg}]\le\varepsilon$; probability of $\mathrm{OmniReg}>\varepsilon$ at most $\delta$ → `UpperExpLE` (an integrable $g\ge$ OmniReg$(A(S))$ with $\int g\,d\mathcal D^n\le\varepsilon$); the failure set's outer measure under $\mathcal D^n$; reason: $S\mapsto\mathrm{OmniReg}(A(S))$ need not be measurable; both coincide with the paper's when it is
--   - encoding: a class $\mathcal H$ of $N$ hypotheses $\mathcal X\to\Delta_K$ → a family $h:\mathrm{Fin}\,N\to(\mathcal X\to\Delta_K)$ of measurable maps, $\mathcal H$ its range; reason: repetitions allowed (a class of at most $N$ hypotheses; the bound is monotone in $N$); measurability makes $\mathbb E\,\ell(h(x),y)$ defined
--   - encoding: randomized predictor $\mathcal X\to\Delta(\Delta_K)$; modeled label $\tilde y\sim p(x)$ → Markov kernel `Kernel X (Simplex K)`; $\mathbb E_{\tilde y\sim a}\ell(\cdot,\tilde y)$ written as $\langle a,\ell(\cdot,\cdot)\rangle$; reason: footnote 3 (p. 19); the modeled-label expectation is exact
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 25, Theorem 3.1 (proof: p. 38, via Theorem 3.8, Lemmas 3.14, 3.16 and A.1)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting
import Definitions.Def_MultiOmniRate_Lipschitz_OmniErrors

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem theorem_3_1.{u} : ∀ (K : ℕ) [NeZero K], 2 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (X : Type u) [MeasurableSpace X] (N : ℕ), 1 ≤ N →
    ∀ (h : Fin N → X → Simplex K), (∀ i, Measurable (h i)) →
    ∀ (n : ℕ), C * (ε ^ (-max ((K : ℝ) - 1) (((K : ℝ) + 2) / 2)) * Real.log (2 / ε) ^ 2 +
        Real.log (2 * N) / ε ^ 2) ≤ n →
    ∃ Alg : (Fin n → X × Fin K) → Kernel X (Simplex K), (∀ S, IsMarkovKernel (Alg S)) ∧
      (∀ (D : Measure (X × Fin K)) [IsProbabilityMeasure D],
        UpperExpLE (Measure.pi fun _ : Fin n => D)
          (fun S => OmniReg (LLip K) (Set.range h) D (Alg S)) ε) ∧
      (∀ (δ : ℝ), 0 < δ → δ < 1 →
        C * (ε ^ (-max ((K : ℝ) - 1) (((K : ℝ) + 2) / 2)) * Real.log (2 / ε) ^ 2 +
          Real.log (2 * N / δ) / ε ^ 2) ≤ n →
        ∀ (D : Measure (X × Fin K)) [IsProbabilityMeasure D],
          (Measure.pi fun _ : Fin n => D) {S | ε < OmniReg (LLip K) (Set.range h) D (Alg S)} ≤
            ENNReal.ofReal δ) := by sorry

end MultiOmniRate.Lipschitz
