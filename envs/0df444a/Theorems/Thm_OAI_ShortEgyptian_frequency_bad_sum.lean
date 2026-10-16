-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_frequency_bad_sum
-- name    : OAI.ShortEgyptian.frequency_bad_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:12:16.105211+00:00
-- url     : https://prove2.me/theorems/36cca5e8-08ab-49a5-9034-3b4c3efcabda
-- title:
--   Counting bound: few elements have a Fourier coefficient above $\delta^3$ at some frequency $l\le\delta^{-4}$
-- statement:
--   Let $\Omega$ be a finite set, $F\colon\Omega\times\mathbb{N}\to\mathbb{C}$ any function, and $\delta>0$, $E\ge0$ real numbers; put $H=\lfloor\delta^{-4}\rfloor$. Suppose that for every integer $l$ with $1\le l\le H$
--
--   $$\sum_{\omega\in\Omega}|F(\omega,l)|^2\le E .$$
--
--   Then the number of $\omega\in\Omega$ having some frequency $l\in\{1,\dots,H\}$ with $|F(\omega,l)|>\delta^3$ is at most $E/\delta^{10}$:
--
--   $$
--   \#\bigl\{\omega\in\Omega:\ \exists\,l\in\{1,\dots,H\},\ |F(\omega,l)|>\delta^3\bigr\}\;\le\;\frac{E}{\delta^{10}} .
--   $$
--
--   This is the unnormalized (counting) form of the union–Markov bound. Summed second moments at each low frequency control how many elements of $\Omega$ are Fourier-bad. It is used with $\Omega$ a window of moduli $u$ and $F(u,l)$ a normalized exponential sum modulo $u$.
--
--   **Formalization Note** The left-hand side is the sum over $\omega$ of an `if … then (1:ℝ) else 0` indicator, i.e. the cardinality as a real number; $H$ is the natural-number floor `⌊1/δ^4⌋₊`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ListSelection.lean#L74-L90

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

theorem OAI.ShortEgyptian.frequency_bad_sum {Ω : Type uΩ} [Fintype Ω]
    (F : Ω → ℕ → ℂ) (δ E : ℝ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmoment : ∀ l ∈ Icc 1 ⌊1/δ^4⌋₊, (∑ ω, ‖F ω l‖^2) ≤ E) :
    (∑ ω, if ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖F ω l‖ then (1:ℝ) else 0) ≤ E/δ^10 := by sorry
