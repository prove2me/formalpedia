-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_phase_second_moment
-- name    : OAI.ShortEgyptian.phase_second_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:37:40.964372+00:00
-- url     : https://prove2.me/theorems/da7f4532-0659-41b4-b800-45f97ce010b6
-- title:
--   Mean-square bound for averages of unimodular sequences with small pairwise correlations
-- statement:
--   Let $\mathcal I$ be a nonempty finite index set with $N=|\mathcal I|$ elements, let $\mathcal U$ be any set, and let $f_i(u)\in\mathbb{C}$ ($i\in\mathcal I$, $u\in\mathcal U$) be complex numbers of modulus one: $|f_i(u)|=1$ for all $i$ and $u$. Let $s\subseteq\mathcal U$ be a finite set and $E\ge0$ a real number, and assume that distinct sequences are almost orthogonal on $s$:
--   $$\Bigl|\sum_{u\in s}f_i(u)\,\overline{f_j(u)}\Bigr|\le E\qquad\text{for all } i\neq j .$$
--   Then
--
--   $$
--   \sum_{u\in s}\Bigl|\frac1N\sum_{i\in\mathcal I}f_i(u)\Bigr|^2\;\le\;\frac{|s|}{N}+E .
--   $$
--
--   This is the basic orthogonality (second-moment) estimate: the averages $\frac1N\sum_if_i(u)$ are small for most $u\in s$ as soon as the sequences $u\mapsto f_i(u)$ have small mutual correlations. The term $|s|/N$ is what perfectly orthogonal sequences would give. It is used with phases of the form $f_i(u)=e(\lambda t_i/u)$, where $e(x)=\exp(2\pi i x)$, to control the mean square of exponential averages over a range of moduli $u$.
--
--   **Formalization Note** The sequences are a function `f : α → β → ℂ` with `‖f i u‖ = 1` for all `i` and `u`; complex conjugation is `starRingEnd ℂ`; the average is the sum divided by `(Fintype.card α : ℂ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DeterministicMean.lean#L86-L129

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

open OAI OAI.ShortEgyptian
universe uα uβ
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.phase_second_moment {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α]
    (s : Finset β) (f : α → β → ℂ) (hnorm : ∀ i u, ‖f i u‖ = 1)
    (E : ℝ) (hE : 0 ≤ E)
    (hcorr : ∀ i j : α, i ≠ j →
      ‖∑ u ∈ s, f i u * (starRingEnd ℂ) (f j u)‖ ≤ E) :
    (∑ u ∈ s, ‖(∑ i, f i u) / (Fintype.card α : ℂ)‖ ^ 2) ≤
      (s.card : ℝ) / Fintype.card α + E := by sorry
