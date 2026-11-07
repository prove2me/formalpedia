-- Prove2me | Theorems.Thm_LDPSelect_lemma_22
-- name    : LDPSelect.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:38.877179+00:00
-- url     : https://prove2.me/theorems/62d24053-cf4b-47d4-b57b-5f9e32a64d03
-- title:
--   Lemma 22 — ray reduction: a private kernel on a finite input set is dominated by a mixture of $2^{|X|}$ rays
-- statement:
--   Let $a\ge1$, let $X$ be a finite input set, and let $Q$ be an $a$-locally private kernel from $X$ to an arbitrary measurable output space. For $S\subseteq X$ let $r_S=1+(a-1)\mathbf 1_S$. There are coefficients $c_S\ge0$ with
--
--   $$\sum_{S\subseteq X}c_S\,r_S(x)=1\qquad\text{for all } x\in X,$$
--
--   defining the private kernel $Q'$ with outputs $S\subseteq X$ and $Q'(S\mid x)=c_S r_S(x)$, such that for every prior $\pi$ on $X$, every payoff $g$ and every threshold $u$, the value $\sup_\varphi\mathbb E[(g(X)-u)\varphi(Z)]$ of the best post-processing is at least as large under $Q'$ as under $Q$: every post-processing $\varphi$ of $Q$ is matched or beaten by some $\psi:2^X\to[0,1]$ of $Q'$.
--
--   This makes the non-interactive optimum of the obstruction instances a finite-dimensional linear program.
--
--   Differences from the source:
--   - encoding: the best post-processing value is at least as large under Q′ as under Q → every post-processing φ of Q is matched or beaten by a post-processing ψ of Q′; reason: Q′ has finitely many outputs, so its supremum is attained and the two statements are equivalent
--   - encoding: a kernel from X; every bounded payoff g → a family of probability measures indexed by the finite type X; every g : X → ℝ; reason: on a finite X a kernel is such a family and every payoff is bounded
--   - encoding: Q′ with at most 2^|X| outputs → Q′ with output set the subsets of X, privacy of Q′ stated as a clause; reason: there are 2^|X| subsets
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Lemma 22, A.5, p.18 (pdf p.19)

import Mathlib
import Definitions.Def_LDPSelect_Fa

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Lemma 22, p.18.

For a finite input set `X`, an `a`-locally private kernel `Q` from `X` to an arbitrary measurable output
space, and `r_S = 1 + (a − 1) 1_S`: there is a private kernel `Q'` with output set `Finset X` and output
likelihood vectors `c_S r_S`, with `c_S ≥ 0` and `∑_S c_S r_S = 1`, such that for every prior, payoff and
threshold the value of the best post-processing is at least as large under `Q'` as under `Q`.

**Formalization Note.** The comparison of suprema is written as: every post-processing `φ` of `Q` is
matched or beaten by a post-processing `ψ` of `Q'`. The supremum under `Q'` is attained, because its
outputs are finite, so this is the same statement. On a finite `X` every payoff is bounded. `Q'(S | x)`
is `c_S r_S(x)`, and its privacy is a clause. -/
theorem lemma_22 {X : Type*} [Fintype X] [DecidableEq X] (a : ℝ) (ha : 1 ≤ a)
    {Z : Type*} [MeasurableSpace Z] (Q : X → Measure Z) [∀ x, IsProbabilityMeasure (Q x)]
    (hQ : ∀ (x x' : X) (A : Set Z), MeasurableSet A → Q x A ≤ ENNReal.ofReal a * Q x' A) :
    ∃ c : Finset X → ℝ, (∀ S, 0 ≤ c S) ∧
      (∀ x, ∑ S, c S * (1 + (a - 1) * (if x ∈ S then 1 else 0)) = 1) ∧
      (∀ (S : Finset X) (x x' : X), c S * (1 + (a - 1) * (if x ∈ S then 1 else 0)) ≤
        a * (c S * (1 + (a - 1) * (if x' ∈ S then 1 else 0)))) ∧
      ∀ (π : X → ℝ), (∀ x, 0 ≤ π x) → ∑ x, π x = 1 → ∀ (g : X → ℝ) (u : ℝ) (φ : Z → ℝ),
        IsPostProcessing φ →
        ∃ ψ : Finset X → ℝ, (∀ S, 0 ≤ ψ S ∧ ψ S ≤ 1) ∧
          ∑ x, π x * (g x - u) * ∫ z, φ z ∂Q x ≤
            ∑ x, π x * (g x - u) *
              ∑ S, ψ S * (c S * (1 + (a - 1) * (if x ∈ S then 1 else 0))) := by sorry

end LDPSelect
