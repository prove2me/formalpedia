-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_badLevel_of_moment
-- name    : OAI.ShortEgyptian.badLevel_of_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T00:18:51.134652+00:00
-- url     : https://prove2.me/theorems/d6e01934-1212-4f58-ba29-00c5299f94c6
-- title:
--   Second-moment bound on the number of Fourier-bad moduli in a window $(X\delta,X]$
-- statement:
--   Let $e(x)=\exp(2\pi i x)$. Let $\mathcal I$ be a finite set, $t\colon\mathcal I\to\mathbb{N}$ a list, $Q\in\mathbb{N}$ a multiplier, and $X,\delta,E$ real numbers with $\delta>0$ and $E\ge0$. Define:
--
--   1. the *window of moduli* $\mathcal W(X,\delta)=\{u\in\mathbb{N}:\ \lfloor X\delta\rfloor+1\le u\le\lfloor X\rfloor\}$;
--   2. the *phase average* $\Phi_t(Q,u,l)=\frac{1}{|\mathcal I|}\sum_{i\in\mathcal I}e\bigl(lQt_i/u\bigr)$ for $u,l\in\mathbb{N}$;
--   3. $u$ is *Fourier-bad* (for $t$, $Q$, $\delta$) if $|\Phi_t(Q,u,l)|>\delta^3$ for some integer $l$ with $1\le l\le\lfloor\delta^{-4}\rfloor$;
--   4. the set of *bad levels* $\mathcal B_t(Q,X,\delta)=\{u\in\mathcal W(X,\delta):\ u\text{ is Fourier-bad}\}$.
--
--   If for every integer $l$ with $1\le l\le\lfloor\delta^{-4}\rfloor$
--
--   $$\sum_{u\in\mathcal W(X,\delta)}\bigl|\Phi_t(Q,u,l)\bigr|^2\le E,$$
--
--   then
--
--   $$
--   \#\,\mathcal B_t(Q,X,\delta)\;\le\;\frac{E}{\delta^{10}} .
--   $$
--
--   The lemma converts a mean-square bound for the exponential sums of a list across a window of moduli, such as the deterministic bound for lists of distinct integers, into an explicit bound on the number of moduli in the window at which the dilated list $Qt_i$ is not well distributed at low frequencies.
--
--   **Formalization Note** $\mathcal W$ is `scaleInterval X δ`, $\Phi$ is `phaseAverage t Q u l`, Fourier-badness is `FourierBad t Q u δ` and $\mathcal B$ is `badLevel t Q X δ`; the floors are natural-number floors `⌊·⌋₊`. Division is total in Lean: if $\mathcal I$ is empty then $\Phi=0$. Every $u\in\mathcal W$ is at least $1$, so no division by $u=0$ occurs in the window.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/LevelSelection.lean#L31-L49

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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection

open OAI OAI.ShortEgyptian
universe uI uΩ uJ uA uD
open scoped BigOperators
open Finset Classical

theorem OAI.ShortEgyptian.badLevel_of_moment {I : Type uI} [Fintype I]
    (t : I → ℕ) (Q : ℕ) (X δ E : ℝ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmoment : ∀ l ∈ Icc 1 ⌊1/δ^4⌋₊,
      (∑ u ∈ scaleInterval X δ, ‖phaseAverage t Q u l‖^2) ≤ E) :
    ((badLevel t Q X δ).card:ℝ) ≤ E/δ^10 := by sorry
