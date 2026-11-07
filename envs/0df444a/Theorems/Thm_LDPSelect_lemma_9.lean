-- Prove2me | Theorems.Thm_LDPSelect_lemma_9
-- name    : LDPSelect.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:42.827273+00:00
-- url     : https://prove2.me/theorems/40e4f03d-caa0-44d4-b38b-fa386ca98d4b
-- title:
--   Lemma 9 — the one-stage lemma: one private report of $X$ against a continuation $s$ is worth $F_a(X,s)$
-- statement:
--   Let $a\ge1$, let $X\ge0$ be integrable with mean $\mu$, and let $s\ge0$. A decision maker obtains one report $Z\sim Q(\cdot\mid X)$ from an $a$-locally private Markov kernel $Q$ into a measurable space, then takes $X$ with probability $\varphi(Z)\in[0,1]$ and $s$ otherwise; write $q(x)=\int\varphi\,dQ(\cdot\mid x)$. Then:
--
--   1. the supremum of the expected payoff $\mathbb E[q(X)X+(1-q(X))s]$ over all output spaces, all private kernels and all post-processings is $F_a(X,s)$ of (1);
--   2. it is attained by binary randomized response to $\{X>s\}$ with "accept on report $1$", or by a constant rule (always accept or always reject);
--   3. if the third term of (1) is strictly larger than $s$ and $\mu$, and $\Pr(X=s)=0$, then every optimal rule has $q=\frac1{a+1}$ almost surely on $\{X<s\}$ and $q=\frac a{a+1}$ almost surely on $\{X>s\}$.
--
--   This is the building block of every Bellman step in the mission: it prices one private report at a single threshold.
--
--   Differences from the source:
--   - encoding: an arbitrary measurable output space → an output type `Z : Type` with a measurable structure; reason: every output space used in the paper lives in `Type`, and the payoff depends on a report only through the acceptance probability it induces
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Lemma 9, p.5 (pdf p.6)

import Mathlib
import Definitions.Def_LDPSelect_Fa

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Lemma 9, p.5.

One `a`-locally private report of `X`, then take `X` or take `s`: the supremum of the expected payoff is
`F_a(X, s)`; it is attained by binary randomized response to `{X > s}` or by a constant rule; and when
the third term of (1) is strictly largest and `Pr(X = s) = 0`, every optimal rule accepts with
probability `1/(a+1)` a.s. on `{X < s}` and `a/(a+1)` a.s. on `{X > s}`.

**Formalization Note.** `a ≥ 1` as in §2. The supremum is an `IsLUB` over every output type `Z : Type`,
Markov private kernel and post-processing. -/
theorem lemma_9 (a : ℝ) (ha : 1 ≤ a) (P : Measure ℝ≥0) [IsProbabilityMeasure P]
    (hP : ∫⁻ x, (x : ℝ≥0∞) ∂P ≠ ⊤) (s : ℝ) (hs : 0 ≤ s) :
    IsLUB {v : ℝ | ∃ (Z : Type) (_ : MeasurableSpace Z) (Q : Kernel ℝ≥0 Z) (φ : Z → ℝ),
        IsMarkovKernel Q ∧ IsPrivateKernel a Q ∧ IsPostProcessing φ ∧ v = stagePayoff P s Q φ}
      (Fa a P s) ∧
    (stagePayoff P s (rrKernel a s) acceptTrue = Fa a P s ∨
      stagePayoff P s (rrKernel a s) (fun _ => 1) = Fa a P s ∨
      stagePayoff P s (rrKernel a s) (fun _ => 0) = Fa a P s) ∧
    (s < faThird a P s → meanOf P < faThird a P s → P {x : ℝ≥0 | (x : ℝ) = s} = 0 →
      ∀ (Z : Type) (_ : MeasurableSpace Z) (Q : Kernel ℝ≥0 Z) (φ : Z → ℝ),
        IsMarkovKernel Q → IsPrivateKernel a Q → IsPostProcessing φ →
        stagePayoff P s Q φ = Fa a P s →
        (∀ᵐ x : ℝ≥0 ∂P, (x : ℝ) < s → acceptProb Q φ x = 1 / (a + 1)) ∧
        (∀ᵐ x : ℝ≥0 ∂P, s < (x : ℝ) → acceptProb Q φ x = a / (a + 1))) := by sorry

end LDPSelect
