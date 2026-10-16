-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_frequency_bad_probability
-- name    : OAI.ShortEgyptian.frequency_bad_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:11:30.975817+00:00
-- url     : https://prove2.me/theorems/f1f5a6ac-3fd7-4a29-b7cb-44316d1fba8f
-- title:
--   Union–Markov bound for the probability of a large Fourier coefficient at some frequency $l\le\delta^{-4}$
-- statement:
--   Let $\Omega$ be a finite set, write $\mathbb{E}_{\omega}$ for the uniform average over $\omega\in\Omega$, and let $F\colon\Omega\times\mathbb{N}\to\mathbb{C}$ be any function. Let $\delta>0$ and $E\ge0$ be real numbers and put $H=\lfloor\delta^{-4}\rfloor$. Suppose that for every integer $l$ with $1\le l\le H$
--
--   $$\mathbb{E}_{\omega}\,|F(\omega,l)|^2\le E .$$
--
--   Then the proportion of $\omega\in\Omega$ for which some frequency $l\in\{1,\dots,H\}$ has $|F(\omega,l)|>\delta^3$ is at most $E/\delta^{10}$:
--
--   $$
--   \mathbb{E}_{\omega}\,\mathbf 1\bigl[\exists\,l\in\{1,\dots,H\}:\ |F(\omega,l)|>\delta^3\bigr]\;\le\;\frac{E}{\delta^{10}} .
--   $$
--
--   Think of $\omega$ as a random choice and of $F(\omega,l)$ as the $l$-th normalized Fourier coefficient of an object built from $\omega$. The lemma turns a second-moment bound at each individual low frequency into a bound on the probability that the object is Fourier-bad, meaning that it has a coefficient larger than $\delta^3$ at some frequency up to $\delta^{-4}$.
--
--   **Formalization Note** $\mathbb{E}_\omega$ is the average `𝔼 ω, _` over a `Fintype`, which equals $0$ when $\Omega$ is empty (the statement is then trivial because $E\ge0$). $H$ is the natural-number floor `⌊1/δ^4⌋₊`, and the indicator is an `if … then (1:ℝ) else 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ListSelection.lean#L20-L56

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection

open OAI OAI.ShortEgyptian
universe uI uΩ uJ uA uE uD uU
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.frequency_bad_probability {Ω : Type uΩ} [Fintype Ω]
    (F : Ω → ℕ → ℂ) (δ E : ℝ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmoment : ∀ l ∈ Icc 1 ⌊1/δ^4⌋₊,
      (𝔼 ω, ‖F ω l‖^2) ≤ E) :
    (𝔼 ω, if ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖F ω l‖ then (1:ℝ) else 0) ≤ E/δ^10 := by sorry
